
#include <bits/stdc++.h>
using namespace std;

using ll = long long;
using db = double;

const db EPS = 1e-9;

struct Parameters {
  int capacity = 70;

  db maxWalkDistance = 0;
  db maxJourneyTime = 0;

  db secPerPassenger = 5;
  db secPerStop = 15;

  // Hard capacity constraint: moves must keep load <= capacity.
  bool hardCapacity = true;
};

struct ProblemData {
  int stopCount = 0;
  int addressCount = 0;
  int walkCount = 0;

  Parameters P;

  vector<int> passengers;                 // passengers[address]
  vector<vector<db>> driveTime;           // driveTime[stop][stop]
  struct WalkOption { int stop; db dist; db time; };
  vector<vector<WalkOption>> walkOptions; // walkOptions[address] list of feasible stops

  // Penalty on route duration (same as your original code).
  // If routeTime <= maxJourneyTime: cost = routeTime.
  // Else: cost is large (encourages feasibility).
  db penalty(db routeTime) const {
    if (routeTime > P.maxJourneyTime + EPS) {
      return P.maxJourneyTime + P.maxJourneyTime * (1.0 + routeTime - P.maxJourneyTime);
    }
    return routeTime;
  }

  // Objective contribution of a route (hard capacity is enforced separately).
  db routeCost(db routeTime, int /*load*/) const {
    return penalty(routeTime);
  }


  db dwell(int w) const {
    return P.secPerStop + P.secPerPassenger * (db)w;
  }
};

struct Route {
  vector<int> stops;
  vector<int> weight; // passengers at corresponding stop visit
};

struct RouteCache {
  vector<db> prefForward;   // sum edges stops[i - 1] -> stops[i]
  vector<db> prefReverse;   // sum edges stops[i] -> stops[i - 1]
  vector<db> prefDwell;     // sum dwell of visits
  vector<int> prefLoad;     // sum weight

  void rebuild(const ProblemData& data, const Route& route) {
    int n = (int)route.stops.size();
    prefForward.assign(n, 0);
    prefReverse.assign(n, 0);
    prefDwell.assign(n, 0);
    prefLoad.assign(n, 0);

    for (int i = 0; i < n; i++) {
      db dw = data.dwell(route.weight[i]);
      prefDwell[i] = dw + (i ? prefDwell[i - 1] : 0);
      prefLoad[i] = route.weight[i] + (i ? prefLoad[i - 1] : 0);

      if (i) {
        prefForward[i] = prefForward[i - 1] + data.driveTime[route.stops[i - 1]][route.stops[i]];
        prefReverse[i] = prefReverse[i - 1] + data.driveTime[route.stops[i]][route.stops[i - 1]];
      }
    }
  }

  // segment [l..r] inclusive, forward internal edges
  db segmentForward(int l, int r) const {
    if (l >= r) return 0;
    return prefForward[r] - prefForward[l];
  }

  // segment [l..r] inclusive, reversed internal edges
  db segmentReverse(int l, int r) const {
    if (l >= r) return 0;
    return prefReverse[r] - prefReverse[l];
  }

  // sum dwell from l..r inclusive
  db segmentDwell(int l, int r) const {
    if (l > r) return 0;
    return prefDwell[r] - (l ? prefDwell[l - 1] : 0);
  }

  // sum load from l..r inclusive
  int segmentLoad(int l, int r) const {
    if (l > r) return 0;
    return prefLoad[r] - (l ? prefLoad[l - 1] : 0);
  }
};

struct Solution {
  vector<Route> routes;
  vector<int> assign;              // assign[address] = stop

  vector<int> routeLoad;
  vector<db> routeTravel;          // internal edges + last -> 0 (NOTE: no depot->first)
  vector<db> routeDwell;           // sum dwell visits
  vector<db> routeTime;            // travel + dwell

  vector<RouteCache> cache;

  vector<db> score;                // score[0] = total objective
};

static db edgeCost(const ProblemData& data, int from, int to) {
  if (from == -1) return 0;
  return data.driveTime[from][to];
}

static void mergeDuplicateStopsInRoute(Route& route) {
  // Sum weights for duplicate stops, keep first appearance order.
  map<int, int> firstPos;
  vector<int> newStops;
  vector<int> newWeight;
  newStops.reserve(route.stops.size());
  newWeight.reserve(route.weight.size());

  for (int i = 0; i < (int)route.stops.size(); i++) {
    int s = route.stops[i];
    int w = route.weight[i];

    auto it = firstPos.find(s);
    if (it == firstPos.end()) {
      firstPos[s] = (int)newStops.size();
      newStops.push_back(s);
      newWeight.push_back(w);
    } else {
      newWeight[it->second] += w;
    }
  }

  route.stops.swap(newStops);
  route.weight.swap(newWeight);
}

static void rebuildRouteMetrics(const ProblemData& data, Solution& sol, int routeId) {
  auto& route = sol.routes[routeId];

  int oldLoad = sol.routeLoad[routeId];
  db oldTime = sol.routeTime[routeId];
  db oldCost = data.routeCost(oldTime, oldLoad);

  int n = (int)route.stops.size();
  int load = 0;
  db dwellSum = 0;
  for (int i = 0; i < n; i++) {
    load += route.weight[i];
    dwellSum += data.dwell(route.weight[i]);
  }

  db travelSum = 0;
  if (n) {
    travelSum += data.driveTime[route.stops.back()][0];
    for (int i = 1; i < n; i++) {
      travelSum += data.driveTime[route.stops[i - 1]][route.stops[i]];
    }
  }

  sol.routeLoad[routeId] = load;
  sol.routeDwell[routeId] = dwellSum;
  sol.routeTravel[routeId] = travelSum;
  sol.routeTime[routeId] = travelSum + dwellSum;

  db newCost = data.routeCost(sol.routeTime[routeId], sol.routeLoad[routeId]);
  sol.score[0] += (newCost - oldCost);

  sol.cache[routeId].rebuild(data, route);
}

static void rebuildAll(const ProblemData& data, Solution& sol) {
  int routeCount = (int)sol.routes.size();

  sol.routeLoad.assign(routeCount, 0);
  sol.routeTravel.assign(routeCount, 0);
  sol.routeDwell.assign(routeCount, 0);
  sol.routeTime.assign(routeCount, 0);
  sol.cache.assign(routeCount, RouteCache{});

  sol.score.assign(1, 0);

  for (int r = 0; r < routeCount; r++) {
    auto& route = sol.routes[r];

    int n = (int)route.stops.size();
    int load = 0;
    db dwellSum = 0;
    for (int i = 0; i < n; i++) {
      load += route.weight[i];
      dwellSum += data.dwell(route.weight[i]);
    }

    db travelSum = 0;
    if (n) {
      travelSum += data.driveTime[route.stops.back()][0];
      for (int i = 1; i < n; i++) {
        travelSum += data.driveTime[route.stops[i - 1]][route.stops[i]];
      }
    }

    sol.routeLoad[r] = load;
    sol.routeDwell[r] = dwellSum;
    sol.routeTravel[r] = travelSum;
    sol.routeTime[r] = travelSum + dwellSum;

    sol.score[0] += data.routeCost(sol.routeTime[r], sol.routeLoad[r]);
    sol.cache[r].rebuild(data, route);
  }
}

static bool validRouteIndex(const Solution& sol, int r);
static bool validPos(const Route& rt, int pos);
static bool validInsertPos(const Route& rt, int pos);
static bool validRange(const Route& rt, int left, int len);

// Best-improvement 2-opt (single pass) for a route; keeps weights aligned with stops.
static bool improveRoute2OptBestOnce(const ProblemData& data, Solution& sol, int r) {
  if (!validRouteIndex(sol, r)) return false;
  auto& route = sol.routes[r];
  int n = (int)route.stops.size();
  if (n < 3) return false;

  const auto& cache = sol.cache[r];
  db oldCost = data.routeCost(sol.routeTime[r], sol.routeLoad[r]);

  db bestDelta = 0;
  int bestI = -1, bestJ = -1;

  for (int i = 0; i < n - 1; i++) {
    for (int j = i + 1; j < n; j++) {
      int a = (i ? route.stops[i - 1] : -1);
      int b = route.stops[i];
      int c = route.stops[j];
      int d = (j + 1 < n ? route.stops[j + 1] : 0);

      db internalForward = cache.segmentForward(i, j);
      db internalReverse = cache.segmentReverse(i, j);

      db deltaTravel = internalReverse - internalForward;
      if (i) deltaTravel += edgeCost(data, a, c) - edgeCost(data, a, b);
      deltaTravel += edgeCost(data, b, d) - edgeCost(data, c, d);

      db newTravel = sol.routeTravel[r] + deltaTravel;
      db newTime = newTravel + sol.routeDwell[r];
      db newCost = data.routeCost(newTime, sol.routeLoad[r]);
      db delta = newCost - oldCost;

      if (delta + EPS < bestDelta) {
        bestDelta = delta;
        bestI = i;
        bestJ = j;
      }
    }
  }

  if (bestI == -1) return false;

  reverse(route.stops.begin() + bestI, route.stops.begin() + bestJ + 1);
  reverse(route.weight.begin() + bestI, route.weight.begin() + bestJ + 1);
  rebuildRouteMetrics(data, sol, r);
  return true;
}

static void improveAllRoutes2Opt(const ProblemData& data, Solution& sol, int maxPasses) {
  for (int pass = 0; pass < maxPasses; pass++) {
    bool improved = false;
    for (int r = 0; r < (int)sol.routes.size(); r++) {
      if (improveRoute2OptBestOnce(data, sol, r)) improved = true;
    }
    if (!improved) break;
  }
}

static bool lexBetter(const vector<db>& a, const vector<db>& b) {
  for (int i = 0; i < (int)a.size(); i++) {
    if (a[i] + EPS < b[i]) return true;
    if (b[i] + EPS < a[i]) return false;
  }
  return false;
}

static bool lexImproves(const vector<db>& delta) {
  for (db v : delta) {
    if (v < -EPS) return true;
    if (v > EPS) return false;
  }
  return false;
}

struct SegmentInfo {
  int firstStop = -1;
  int lastStop = -1;
  db internalForward = 0;
  db internalReverse = 0;
  db dwellSum = 0;
  int loadSum = 0;
  int len = 0;
};

static SegmentInfo getSegmentInfo(const ProblemData& data, const Solution& sol, int routeId, int left, int len) {
  const auto& route = sol.routes[routeId];
  const auto& cache = sol.cache[routeId];

  int right = left + len - 1;
  SegmentInfo info;

  info.len = len;
  info.firstStop = route.stops[left];
  info.lastStop = route.stops[right];
  info.internalForward = cache.segmentForward(left, right);
  info.internalReverse = cache.segmentReverse(left, right);
  info.dwellSum = cache.segmentDwell(left, right);
  info.loadSum = cache.segmentLoad(left, right);

  return info;
}

static db deltaRemoveSegmentTravel(const ProblemData& data, const Solution& sol, int routeId, int left, int right) {
  const auto& route = sol.routes[routeId];
  const auto& cache = sol.cache[routeId];

  int prev = (left ? route.stops[left - 1] : -1);
  int first = route.stops[left];
  int last = route.stops[right];
  int next = (right + 1 < (int)route.stops.size() ? route.stops[right + 1] : 0);

  db internal = cache.segmentForward(left, right);
  db delta = 0;

  delta -= internal;
  if (left) delta -= edgeCost(data, prev, first);
  delta -= edgeCost(data, last, next);
  if (left) delta += edgeCost(data, prev, next);

  return delta;
}

static db deltaInsertSegmentTravel(const ProblemData& data, const Solution& sol, int routeId, int pos, int segFirst, int segLast, db internal) {
  const auto& route = sol.routes[routeId];
  int n = (int)route.stops.size();

  if (!n) {
    return internal + edgeCost(data, segLast, 0);
  }

  if (pos == 0) {
    int oldFirst = route.stops[0];
    return internal + edgeCost(data, segLast, oldFirst);
  }

  if (pos == n) {
    int oldLast = route.stops[n - 1];
    return -edgeCost(data, oldLast, 0) + edgeCost(data, oldLast, segFirst) + internal + edgeCost(data, segLast, 0);
  }

  int prev = route.stops[pos - 1];
  int next = route.stops[pos];
  return -edgeCost(data, prev, next) + edgeCost(data, prev, segFirst) + internal + edgeCost(data, segLast, next);
}

static db deltaReplaceSegmentTravel(const ProblemData& data, const Solution& sol, int routeId, int left, int right, const SegmentInfo& newSeg, bool reverseNew) {
  const auto& route = sol.routes[routeId];
  const auto& cache = sol.cache[routeId];

  int prev = (left ? route.stops[left - 1] : -1);
  int oldFirst = route.stops[left];
  int oldLast = route.stops[right];
  int next = (right + 1 < (int)route.stops.size() ? route.stops[right + 1] : 0);

  db oldInternal = cache.segmentForward(left, right);

  int newFirst = reverseNew ? newSeg.lastStop : newSeg.firstStop;
  int newLast = reverseNew ? newSeg.firstStop : newSeg.lastStop;
  db newInternal = reverseNew ? newSeg.internalReverse : newSeg.internalForward;

  db delta = 0;
  delta += newInternal - oldInternal;
  if (left) delta += edgeCost(data, prev, newFirst) - edgeCost(data, prev, oldFirst);
  delta += edgeCost(data, newLast, next) - edgeCost(data, oldLast, next);

  return delta;
}

static bool capacityOk(const ProblemData& data, int load) {
  return load <= data.P.capacity;
}

static bool enforceCapacity(const ProblemData& data, int newLoad) {
  if (!data.P.hardCapacity) return true;
  return capacityOk(data, newLoad);
}

static bool cleanupEmptyRoutes(Solution& sol) {
  size_t before = sol.routes.size();
  sol.routes.erase(
      remove_if(sol.routes.begin(), sol.routes.end(),
                [](const Route& r) { return r.stops.empty(); }),
      sol.routes.end());
  return sol.routes.size() != before;
}

static bool validRouteIndex(const Solution& sol, int r) {
  return 0 <= r && r < (int)sol.routes.size();
}

static bool validPos(const Route& rt, int pos) {
  return 0 <= pos && pos < (int)rt.stops.size();
}

static bool validInsertPos(const Route& rt, int pos) {
  return 0 <= pos && pos <= (int)rt.stops.size();
}

static bool validRange(const Route& rt, int left, int len) {
  if (len <= 0) return false;
  if (left < 0) return false;
  return left + len <= (int)rt.stops.size();
}

struct Timer {
  chrono::steady_clock::time_point deadline;

  void set_limit_seconds(double sec) {
    auto start = chrono::steady_clock::now();
    deadline = start + chrono::milliseconds((ll)(sec * 1000.0));
  }

  bool time_up() const {
    return chrono::steady_clock::now() >= deadline;
  }
};

// =======================
// Move payloads
// =======================
enum class MoveType {
  Relocate1,     // (a) one-point relocate
  Swap2,         // (b) two-point swap
  TwoOptIntra,   // (c) two-opt within route
  TwoOptInter,   // (c) 2-opt* between routes (exchange suffix)
  OrOpt,         // (d) Or-opt (len 2..4), intra/inter, can optionally reverse segment
  ReassignAddress, // (d.3) reassign one address to another feasible stop
  StopMerge,     // (d.4) merge all addresses from one stop into another
  SplitRoute,    // (d.5) split a route into two routes
  ThreeOpt,      // (e) three-opt within route
  ThreePoint,    // (f) swap adjacent pair with a third node
  CrossExchange, // (g) cross-exchange between two routes
  KExchange,     // LNS ruin & recreate (k nodes)
};

struct Relocate1Move { int fromRoute, fromPos, toRoute, toPos; }; // toRoute can be == routeCount meaning NEW
struct Swap2Move { int r1, p1, r2, p2; };
struct TwoOptIntraMove { int route, left, right; };

struct TwoOptInterMove {
  int rA, cutA; // suffix starts at cutA+1 (can be empty if cutA==nA-1)
  int rB, cutB;
  bool reverseAtoB = false; // reverse suffix of A when inserting into B
  bool reverseBtoA = false; // reverse suffix of B when inserting into A
};

struct OrOptMove {
  int fromRoute, left, len;
  int toRoute, pos; // toRoute can be NEW (==routeCount); pos in [0..sizeAfter] for intra, [0..nB] for inter, 0 for NEW
  bool reverseSeg = false;
};

struct ReassignAddressMove {
  int address = -1;
  int oldStop = -1;
  int newStop = -1;
  int removeRoute = -1;
  int removePos = -1;
  bool removeStop = false;
  int addRoute = -1; // -1 means create a new route
  int addPos = 0;    // position in addRoute after removal if addRoute == removeRoute
  bool addExisting = false;
};

struct StopMergeMove {
  int oldStop = -1;
  int newStop = -1;
  int addRoute = -1; // -1 means create a new route
  int addPos = 0;    // position of newStop in addRoute (after removal), or insertion pos if missing
  bool addExisting = true;
};

struct SplitRouteMove { int route, cut; };

struct ThreeOptMove {
  int route;
  int a, b, c;  // cut AFTER a, AFTER b, AFTER c (0-based, a<b<c)
  int pattern;  // 1..7 (see code)
};

struct ThreePointMove {
  int rPair, posPair; // pair at posPair, posPair+1 in rPair
  int rSingle, posSingle;
  bool reversePair = false;
};

struct CrossExchangeMove {
  int rA, leftA, lenA;
  int rB, leftB, lenB;
  bool reverseIntoA = false; // reverse segment from B when inserting into A
  bool reverseIntoB = false; // reverse segment from A when inserting into B
};

struct KExchangeMove {
  // Replace a subset of existing routes and optionally append new routes (without copying the whole Solution).
  vector<int> routeIds;        // indices in the CURRENT solution to replace
  vector<Route> newRoutes;     // replacement routes, same length as routeIds
  vector<Route> appended;      // extra routes to append
};

using MovePayload = variant<
  Relocate1Move,
  Swap2Move,
  TwoOptIntraMove,
  TwoOptInterMove,
  OrOptMove,
  ReassignAddressMove,
  StopMergeMove,
  SplitRouteMove,
  ThreeOptMove,
  ThreePointMove,
  CrossExchangeMove,
  KExchangeMove
>;

struct Candidate {
  int opId = -1;
  MoveType type;
  vector<db> delta;   // delta objective(s)
  MovePayload payload;
};

// =======================
// Operator interface
// =======================
struct MoveOperator {
  virtual ~MoveOperator() = default;
  virtual string name() const = 0;
  virtual db weight() const { return 1.0; }

  // Sample ONE random move and write Candidate (delta + payload). Return false if cannot sample.
  virtual bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const = 0;

  // Apply the sampled move to solution (assumes it was evaluated on the same sol state).
  virtual void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const = 0;
};

// =======================
// (a) Relocate one node
// =======================
struct Relocate1Operator : MoveOperator {
  db w = 1.0;
  db pNewRoute = 0.10; // probability to move into a brand-new route

  string name() const override { return "Relocate1"; }
  db weight() const override { return w; }

  static int stopAfterRemoval(const Route& route, int removedPos, int idx) {
    // route size n, after removing position removedPos, new size n-1
    if (idx < removedPos) return route.stops[idx];
    return route.stops[idx + 1];
  }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);

    int fromRoute = -1;
    for (int tries = 0; tries < 20; tries++) {
      int r = pickRoute(rng);
      if (!sol.routes[r].stops.empty()) { fromRoute = r; break; }
    }
    if (fromRoute == -1) return false;

    const auto& A = sol.routes[fromRoute];
    int nA = (int)A.stops.size();

    uniform_int_distribution<int> pickPosA(0, nA - 1);
    int fromPos = pickPosA(rng);

    int stop = A.stops[fromPos];
    int wt = A.weight[fromPos];

    bool toNew = (uniform_real_distribution<db>(0, 1)(rng) < pNewRoute);

    int toRoute = -1;
    int toPos = 0;

    if (toNew) {
      toRoute = R; // NEW
      toPos = 0;
    } else {
      uniform_int_distribution<int> pickToRoute(0, R - 1);
      toRoute = pickToRoute(rng);

      if (toRoute == fromRoute) {
        if (nA == 1) return false;
        // insertion index in route AFTER removal, size = nA-1, allowed [0..nA-1]
        uniform_int_distribution<int> pickIns(0, nA - 1);
        toPos = pickIns(rng);
      } else {
        int nB = (int)sol.routes[toRoute].stops.size();
        uniform_int_distribution<int> pickIns(0, nB);
        toPos = pickIns(rng);
      }
    }

    vector<db> delta(1, 0);

    if (toRoute == R) {
      // Move stop into new route
      int newLoadA = sol.routeLoad[fromRoute] - wt;
      if (!enforceCapacity(data, newLoadA)) return false;

      db deltaTravelA = deltaRemoveSegmentTravel(data, sol, fromRoute, fromPos, fromPos);
      db newTravelA = sol.routeTravel[fromRoute] + deltaTravelA;
      db newDwellA = sol.routeDwell[fromRoute] - data.dwell(wt);
      db newTimeA = newTravelA + newDwellA;

      db oldCostA = data.routeCost(sol.routeTime[fromRoute], sol.routeLoad[fromRoute]);
      db newCostA = data.routeCost(newTimeA, newLoadA);

      // new route with single node
      int newLoadN = wt;
      if (!enforceCapacity(data, newLoadN)) return false;

      db newTravelN = edgeCost(data, stop, 0);
      db newDwellN = data.dwell(wt);
      db newTimeN = newTravelN + newDwellN;
      db newCostN = data.routeCost(newTimeN, newLoadN);

      delta[0] = (newCostA - oldCostA) + newCostN;

      out.opId = out.opId; // filled by caller
      out.type = MoveType::Relocate1;
      out.delta = delta;
      out.payload = Relocate1Move{fromRoute, fromPos, toRoute, toPos};
      return true;
    }

    if (toRoute != fromRoute) {
      int newLoadA = sol.routeLoad[fromRoute] - wt;
      int newLoadB = sol.routeLoad[toRoute] + wt;
      if (!enforceCapacity(data, newLoadA) || !enforceCapacity(data, newLoadB)) return false;

      db deltaTravelA = deltaRemoveSegmentTravel(data, sol, fromRoute, fromPos, fromPos);
      db deltaTravelB = deltaInsertSegmentTravel(data, sol, toRoute, toPos, stop, stop, 0);

      db newTravelA = sol.routeTravel[fromRoute] + deltaTravelA;
      db newTravelB = sol.routeTravel[toRoute] + deltaTravelB;

      db newDwellA = sol.routeDwell[fromRoute] - data.dwell(wt);
      db newDwellB = sol.routeDwell[toRoute] + data.dwell(wt);

      db newTimeA = newTravelA + newDwellA;
      db newTimeB = newTravelB + newDwellB;

      db oldCostA = data.routeCost(sol.routeTime[fromRoute], sol.routeLoad[fromRoute]);
      db oldCostB = data.routeCost(sol.routeTime[toRoute], sol.routeLoad[toRoute]);

      db newCostA = data.routeCost(newTimeA, newLoadA);
      db newCostB = data.routeCost(newTimeB, newLoadB);

      delta[0] = (newCostA - oldCostA) + (newCostB - oldCostB);

      out.type = MoveType::Relocate1;
      out.delta = delta;
      out.payload = Relocate1Move{fromRoute, fromPos, toRoute, toPos};
      return true;
    }

    // Intra-route relocate
    // Compute delta by sequential remove + insert on after-removal adjacency (O(1)).
    int i = fromPos;
    int pos = toPos; // insertion index in after-removal route, size nA-1, allowed [0..nA-1]
    if (nA <= 1) return false;

    // Removal delta on original
    db deltaRemove = deltaRemoveSegmentTravel(data, sol, fromRoute, i, i);

    // Insertion into after-removal
    int sizeAfter = nA - 1;

    // Determine neighbors in after-removal at insertion position pos
    db deltaInsert = 0;
    if (sizeAfter == 0) {
      // was nA==1, already filtered
      deltaInsert = edgeCost(data, stop, 0);
    } else if (pos == 0) {
      int next = stopAfterRemoval(A, i, 0);
      deltaInsert = edgeCost(data, stop, next);
    } else if (pos == sizeAfter) {
      int prev = stopAfterRemoval(A, i, sizeAfter - 1);
      deltaInsert = -edgeCost(data, prev, 0) + edgeCost(data, prev, stop) + edgeCost(data, stop, 0);
    } else {
      int prev = stopAfterRemoval(A, i, pos - 1);
      int next = stopAfterRemoval(A, i, pos);
      deltaInsert = -edgeCost(data, prev, next) + edgeCost(data, prev, stop) + edgeCost(data, stop, next);
    }

    db newTravel = sol.routeTravel[fromRoute] + deltaRemove + deltaInsert;
    db newTime = newTravel + sol.routeDwell[fromRoute];

    db oldCost = data.routeCost(sol.routeTime[fromRoute], sol.routeLoad[fromRoute]);
    db newCost = data.routeCost(newTime, sol.routeLoad[fromRoute]);

    delta[0] = newCost - oldCost;

    out.type = MoveType::Relocate1;
    out.delta = delta;
    out.payload = Relocate1Move{fromRoute, fromPos, toRoute, toPos};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<Relocate1Move>(cand.payload);

    int R = (int)sol.routes.size();
    int fromRoute = mv.fromRoute;
    int toRoute = mv.toRoute;
    int fromPos = mv.fromPos;
    int toPos = mv.toPos;

    if (!validRouteIndex(sol, fromRoute)) return;
    if (!validPos(sol.routes[fromRoute], fromPos)) return;
    if (toRoute != R && !validRouteIndex(sol, toRoute)) return;

    if (toRoute == R) {
      // create new route
      Route nr;
      int stop = sol.routes[fromRoute].stops[fromPos];
      int wt = sol.routes[fromRoute].weight[fromPos];
      nr.stops.push_back(stop);
      nr.weight.push_back(wt);

      sol.routes.push_back(nr);

      // remove from A
      auto& A = sol.routes[fromRoute];
      A.stops.erase(A.stops.begin() + fromPos);
      A.weight.erase(A.weight.begin() + fromPos);


      bool removed = cleanupEmptyRoutes(sol);
      rebuildAll(data, sol);
      (void)removed;
      return;
    }

    if (toRoute != fromRoute) {
      auto& A = sol.routes[fromRoute];
      auto& B = sol.routes[toRoute];

      int stop = A.stops[fromPos];
      int wt = A.weight[fromPos];

      A.stops.erase(A.stops.begin() + fromPos);
      A.weight.erase(A.weight.begin() + fromPos);

      if (!validInsertPos(B, toPos)) return;
      B.stops.insert(B.stops.begin() + toPos, stop);
      B.weight.insert(B.weight.begin() + toPos, wt);


      bool removed = cleanupEmptyRoutes(sol);
      rebuildAll(data, sol);
      (void)removed;
      return;
    }

    // Intra-route
    auto& A = sol.routes[fromRoute];
    int stop = A.stops[fromPos];
    int wt = A.weight[fromPos];

    A.stops.erase(A.stops.begin() + fromPos);
    A.weight.erase(A.weight.begin() + fromPos);

    int sizeAfter = (int)A.stops.size(); // nA-1
    int pos = min(max(toPos, 0), sizeAfter);
    A.stops.insert(A.stops.begin() + pos, stop);
    A.weight.insert(A.weight.begin() + pos, wt);

    rebuildAll(data, sol);
  }
};

// =======================
// (b) Swap two nodes
// =======================
struct Swap2Operator : MoveOperator {
  db w = 1.0;
  string name() const override { return "Swap2"; }
  db weight() const override { return w; }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);

    int r1 = -1, r2 = -1;
    for (int tries = 0; tries < 50; tries++) {
      int a = pickRoute(rng), b = pickRoute(rng);
      if (sol.routes[a].stops.empty() || sol.routes[b].stops.empty()) continue;
      r1 = a; r2 = b;
      break;
    }
    if (r1 == -1) return false;

    const auto& A = sol.routes[r1];
    const auto& B = sol.routes[r2];

    uniform_int_distribution<int> pickPosA(0, (int)A.stops.size() - 1);
    uniform_int_distribution<int> pickPosB(0, (int)B.stops.size() - 1);

    int p1 = pickPosA(rng);
    int p2 = pickPosB(rng);

    vector<db> delta(1, 0);

    if (r1 != r2) {
      auto segA = getSegmentInfo(data, sol, r1, p1, 1);
      auto segB = getSegmentInfo(data, sol, r2, p2, 1);

      int newLoadA = sol.routeLoad[r1] - segA.loadSum + segB.loadSum;
      int newLoadB = sol.routeLoad[r2] - segB.loadSum + segA.loadSum;
      if (!enforceCapacity(data, newLoadA) || !enforceCapacity(data, newLoadB)) return false;

      db deltaTravelA = deltaReplaceSegmentTravel(data, sol, r1, p1, p1, segB, false);
      db deltaTravelB = deltaReplaceSegmentTravel(data, sol, r2, p2, p2, segA, false);

      db newTravelA = sol.routeTravel[r1] + deltaTravelA;
      db newTravelB = sol.routeTravel[r2] + deltaTravelB;

      db newDwellA = sol.routeDwell[r1] - segA.dwellSum + segB.dwellSum;
      db newDwellB = sol.routeDwell[r2] - segB.dwellSum + segA.dwellSum;

      db newTimeA = newTravelA + newDwellA;
      db newTimeB = newTravelB + newDwellB;

      db oldCostA = data.routeCost(sol.routeTime[r1], sol.routeLoad[r1]);
      db oldCostB = data.routeCost(sol.routeTime[r2], sol.routeLoad[r2]);
      db newCostA = data.routeCost(newTimeA, newLoadA);
      db newCostB = data.routeCost(newTimeB, newLoadB);

      delta[0] = (newCostA - oldCostA) + (newCostB - oldCostB);

      out.type = MoveType::Swap2;
      out.delta = delta;
      out.payload = Swap2Move{r1, p1, r2, p2};
      return true;
    }

    // Intra-route swap
    int n = (int)A.stops.size();
    if (n < 2) return false;
    if (p1 == p2) return false;
    int i = min(p1, p2);
    int j = max(p1, p2);

    int x = A.stops[i];
    int y = A.stops[j];

    int a = (i ? A.stops[i - 1] : -1);
    int c = (i + 1 < n ? A.stops[i + 1] : 0);

    int d = A.stops[j - 1];
    int f = (j + 1 < n ? A.stops[j + 1] : 0);

    db deltaTravel = 0;

    if (i + 1 == j) {
      // adjacent: ... a - x - y - f
      if (i) deltaTravel += edgeCost(data, a, y) - edgeCost(data, a, x);
      deltaTravel += edgeCost(data, y, x) - edgeCost(data, x, y);
      deltaTravel += edgeCost(data, x, f) - edgeCost(data, y, f);
    } else {
      if (i) deltaTravel += edgeCost(data, a, y) - edgeCost(data, a, x);
      deltaTravel += edgeCost(data, y, c) - edgeCost(data, x, c);
      deltaTravel += edgeCost(data, d, x) - edgeCost(data, d, y);
      deltaTravel += edgeCost(data, x, f) - edgeCost(data, y, f);
    }

    db newTravel = sol.routeTravel[r1] + deltaTravel;
    db newTime = newTravel + sol.routeDwell[r1];

    db oldCost = data.routeCost(sol.routeTime[r1], sol.routeLoad[r1]);
    db newCost = data.routeCost(newTime, sol.routeLoad[r1]);
    delta[0] = newCost - oldCost;

    out.type = MoveType::Swap2;
    out.delta = delta;
    out.payload = Swap2Move{r1, p1, r2, p2};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<Swap2Move>(cand.payload);
    int r1 = mv.r1, r2 = mv.r2;
    int p1 = mv.p1, p2 = mv.p2;

    if (!validRouteIndex(sol, r1) || !validRouteIndex(sol, r2)) return;
    if (!validPos(sol.routes[r1], p1) || !validPos(sol.routes[r2], p2)) return;

    if (r1 == r2) {
      auto& A = sol.routes[r1];
      swap(A.stops[p1], A.stops[p2]);
      swap(A.weight[p1], A.weight[p2]);
      rebuildAll(data, sol);
      return;
    }

    auto& A = sol.routes[r1];
    auto& B = sol.routes[r2];
    swap(A.stops[p1], B.stops[p2]);
    swap(A.weight[p1], B.weight[p2]);


    bool removed = cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
    (void)removed;
  }
};

// =======================
// (c) Two-opt intra (reverse [i..j])
// =======================
struct TwoOptIntraOperator : MoveOperator {
  db w = 1.0;
  string name() const override { return "TwoOptIntra"; }
  db weight() const override { return w; }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);
    int r = -1;
    for (int tries = 0; tries < 20; tries++) {
      int rr = pickRoute(rng);
      if ((int)sol.routes[rr].stops.size() >= 3) { r = rr; break; }
    }
    if (r == -1) return false;

    const auto& route = sol.routes[r];
    int n = (int)route.stops.size();

    uniform_int_distribution<int> pickLeft(0, n - 2);
    int i = pickLeft(rng);

    uniform_int_distribution<int> pickRight(i + 1, n - 1);
    int j = pickRight(rng);

    int a = (i ? route.stops[i - 1] : -1);
    int b = route.stops[i];
    int c = route.stops[j];
    int d = (j + 1 < n ? route.stops[j + 1] : 0);

    db internalForward = sol.cache[r].segmentForward(i, j);
    db internalReverse = sol.cache[r].segmentReverse(i, j);

    db deltaTravel = internalReverse - internalForward;
    if (i) deltaTravel += edgeCost(data, a, c) - edgeCost(data, a, b);
    deltaTravel += edgeCost(data, b, d) - edgeCost(data, c, d);

    db newTravel = sol.routeTravel[r] + deltaTravel;
    db newTime = newTravel + sol.routeDwell[r];

    db oldCost = data.routeCost(sol.routeTime[r], sol.routeLoad[r]);
    db newCost = data.routeCost(newTime, sol.routeLoad[r]);

    vector<db> delta = { newCost - oldCost };

    out.type = MoveType::TwoOptIntra;
    out.delta = delta;
    out.payload = TwoOptIntraMove{r, i, j};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<TwoOptIntraMove>(cand.payload);
    if (!validRouteIndex(sol, mv.route)) return;
    auto& route = sol.routes[mv.route];

    if (mv.left < 0 || mv.right >= (int)route.stops.size() || mv.left >= mv.right) return;
    reverse(route.stops.begin() + mv.left, route.stops.begin() + mv.right + 1);
    reverse(route.weight.begin() + mv.left, route.weight.begin() + mv.right + 1);

    rebuildAll(data, sol);
  }
};

// =======================
// (c) Two-opt inter (2-opt*): exchange suffixes of two routes
// =======================
struct TwoOptInterOperator : MoveOperator {
  db w = 1.0;
  db pReverse = 0.25; // probability to reverse an exchanged suffix
  string name() const override { return "TwoOptInter"; }
  db weight() const override { return w; }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R < 2) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);

    int rA = -1, rB = -1;
    for (int tries = 0; tries < 50; tries++) {
      int a = pickRoute(rng), b = pickRoute(rng);
      if (a == b) continue;
      if (sol.routes[a].stops.empty() || sol.routes[b].stops.empty()) continue;
      rA = a; rB = b;
      break;
    }
    if (rA == -1) return false;

    int nA = (int)sol.routes[rA].stops.size();
    int nB = (int)sol.routes[rB].stops.size();

    uniform_int_distribution<int> pickCutA(0, nA - 1);
    uniform_int_distribution<int> pickCutB(0, nB - 1);

    int cutA = pickCutA(rng);
    int cutB = pickCutB(rng);

    bool revA = (uniform_real_distribution<db>(0, 1)(rng) < pReverse);
    bool revB = (uniform_real_distribution<db>(0, 1)(rng) < pReverse);

    // Suffix ranges
    int aL = cutA + 1;
    int bL = cutB + 1;

    // Precompute prefix metrics for A[0..cutA], B[0..cutB]
    const auto& cacheA = sol.cache[rA];
    const auto& cacheB = sol.cache[rB];
    const auto& routeA = sol.routes[rA];
    const auto& routeB = sol.routes[rB];

    // Prefix internal travel
    db prefTravelA = cacheA.segmentForward(0, cutA);
    db prefTravelB = cacheB.segmentForward(0, cutB);

    db prefDwellA = cacheA.segmentDwell(0, cutA);
    db prefDwellB = cacheB.segmentDwell(0, cutB);

    int prefLoadA = cacheA.segmentLoad(0, cutA);
    int prefLoadB = cacheB.segmentLoad(0, cutB);

    // Suffix info (can be empty)
    auto suffixInfo = [&](int r, int l, bool rev) -> SegmentInfo {
      SegmentInfo info;
      const auto& rt = sol.routes[r];
      if (l >= (int)rt.stops.size()) {
        info.len = 0;
        return info;
      }
      info = getSegmentInfo(data, sol, r, l, (int)rt.stops.size() - l);
      return info;
    };

    SegmentInfo sufA = suffixInfo(rA, aL, false);
    SegmentInfo sufB = suffixInfo(rB, bL, false);

    // Build new route A = prefixA + suffixB (maybe reversed)
    auto sufFirst = [&](const SegmentInfo& s, bool rev) -> int {
      if (s.len == 0) return -1;
      return rev ? s.lastStop : s.firstStop;
    };
    auto sufLast = [&](const SegmentInfo& s, bool rev) -> int {
      if (s.len == 0) return -1;
      return rev ? s.firstStop : s.lastStop;
    };
    auto sufInternal = [&](const SegmentInfo& s, bool rev) -> db {
      if (s.len == 0) return 0;
      return rev ? s.internalReverse : s.internalForward;
    };

    int lastPrefA = routeA.stops[cutA];
    int lastPrefB = routeB.stops[cutB];

    // New A travel
    db newTravelA = prefTravelA;
    db newDwellA = prefDwellA;
    int newLoadA = prefLoadA;

    if (sufB.len > 0) {
      newTravelA += edgeCost(data, lastPrefA, sufFirst(sufB, revB));
      newTravelA += sufInternal(sufB, revB);
      newTravelA += edgeCost(data, sufLast(sufB, revB), 0);
      newDwellA += sufB.dwellSum;
      newLoadA += sufB.loadSum;
    } else {
      newTravelA += edgeCost(data, lastPrefA, 0);
    }

    // New B travel
    db newTravelB = prefTravelB;
    db newDwellB = prefDwellB;
    int newLoadB = prefLoadB;

    if (sufA.len > 0) {
      newTravelB += edgeCost(data, lastPrefB, sufFirst(sufA, revA));
      newTravelB += sufInternal(sufA, revA);
      newTravelB += edgeCost(data, sufLast(sufA, revA), 0);
      newDwellB += sufA.dwellSum;
      newLoadB += sufA.loadSum;
    } else {
      newTravelB += edgeCost(data, lastPrefB, 0);
    }

    if (!enforceCapacity(data, newLoadA) || !enforceCapacity(data, newLoadB)) return false;

    db newTimeA = newTravelA + newDwellA;
    db newTimeB = newTravelB + newDwellB;

    db oldCostA = data.routeCost(sol.routeTime[rA], sol.routeLoad[rA]);
    db oldCostB = data.routeCost(sol.routeTime[rB], sol.routeLoad[rB]);

    db newCostA = data.routeCost(newTimeA, newLoadA);
    db newCostB = data.routeCost(newTimeB, newLoadB);

    vector<db> delta = { (newCostA - oldCostA) + (newCostB - oldCostB) };

    out.type = MoveType::TwoOptInter;
    out.delta = delta;
    out.payload = TwoOptInterMove{rA, cutA, rB, cutB, revA, revB};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<TwoOptInterMove>(cand.payload);

    int rA = mv.rA, rB = mv.rB;
    int cutA = mv.cutA, cutB = mv.cutB;

    if (!validRouteIndex(sol, rA) || !validRouteIndex(sol, rB) || rA == rB) return;
    auto& A = sol.routes[rA];
    auto& B = sol.routes[rB];

    if (cutA < 0 || cutA >= (int)A.stops.size()) return;
    if (cutB < 0 || cutB >= (int)B.stops.size()) return;

    int aL = cutA + 1;
    int bL = cutB + 1;

    vector<int> tailAStops, tailAWeight, tailBStops, tailBWeight;

    if (aL < (int)A.stops.size()) {
      tailAStops.assign(A.stops.begin() + aL, A.stops.end());
      tailAWeight.assign(A.weight.begin() + aL, A.weight.end());
      A.stops.erase(A.stops.begin() + aL, A.stops.end());
      A.weight.erase(A.weight.begin() + aL, A.weight.end());
    }

    if (bL < (int)B.stops.size()) {
      tailBStops.assign(B.stops.begin() + bL, B.stops.end());
      tailBWeight.assign(B.weight.begin() + bL, B.weight.end());
      B.stops.erase(B.stops.begin() + bL, B.stops.end());
      B.weight.erase(B.weight.begin() + bL, B.weight.end());
    }

    if (mv.reverseBtoA) {
      reverse(tailBStops.begin(), tailBStops.end());
      reverse(tailBWeight.begin(), tailBWeight.end());
    }
    if (mv.reverseAtoB) {
      reverse(tailAStops.begin(), tailAStops.end());
      reverse(tailAWeight.begin(), tailAWeight.end());
    }

    A.stops.insert(A.stops.end(), tailBStops.begin(), tailBStops.end());
    A.weight.insert(A.weight.end(), tailBWeight.begin(), tailBWeight.end());

    B.stops.insert(B.stops.end(), tailAStops.begin(), tailAStops.end());
    B.weight.insert(B.weight.end(), tailAWeight.begin(), tailAWeight.end());


    bool removed = cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
    (void)removed;
  }
};

// =======================
// (d) Or-opt: move a segment len=2..4 (intra/inter), optional reverse
// =======================
struct OrOptOperator : MoveOperator {
  db w = 1.0;
  int minLen = 2, maxLen = 4;
  db pReverse = 0.25;
  db pNewRoute = 0.05;

  string name() const override { return "OrOpt"; }
  db weight() const override { return w; }

  static int stopAfterRemovalSeg(const Route& route, int left, int len, int idx) {
    // after removing [left..left+len-1], new index idx in [0..n-len-1]
    if (idx < left) return route.stops[idx];
    return route.stops[idx + len];
  }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);

    int fromRoute = -1;
    for (int tries = 0; tries < 30; tries++) {
      int r = pickRoute(rng);
      if ((int)sol.routes[r].stops.size() >= minLen) { fromRoute = r; break; }
    }
    if (fromRoute == -1) return false;

    const auto& A = sol.routes[fromRoute];
    int nA = (int)A.stops.size();

    int upperLen = min(maxLen, nA);
    uniform_int_distribution<int> pickLen(minLen, upperLen);
    int len = pickLen(rng);

    uniform_int_distribution<int> pickLeft(0, nA - len);
    int left = pickLeft(rng);

    bool reverseSeg = (uniform_real_distribution<db>(0, 1)(rng) < pReverse);

    bool toNew = (uniform_real_distribution<db>(0, 1)(rng) < pNewRoute);
    int toRoute = -1;
    int pos = 0;

    if (toNew) {
      toRoute = R; // NEW
      pos = 0;
    } else {
      uniform_int_distribution<int> pickToRoute(0, R - 1);
      toRoute = pickToRoute(rng);

      if (toRoute == fromRoute) {
        int sizeAfter = nA - len;
        uniform_int_distribution<int> pickPos(0, sizeAfter);
        pos = pickPos(rng);
      } else {
        int nB = (int)sol.routes[toRoute].stops.size();
        uniform_int_distribution<int> pickPos(0, nB);
        pos = pickPos(rng);
      }
    }

    vector<db> delta(1, 0);

    auto seg = getSegmentInfo(data, sol, fromRoute, left, len);
    int segFirst = reverseSeg ? seg.lastStop : seg.firstStop;
    int segLast = reverseSeg ? seg.firstStop : seg.lastStop;
    db segInternal = reverseSeg ? seg.internalReverse : seg.internalForward;

    if (toRoute == R) {
      // create new route from segment (as a chain)
      int newLoadA = sol.routeLoad[fromRoute] - seg.loadSum;
      if (!enforceCapacity(data, newLoadA)) return false;

      db deltaTravelA = deltaRemoveSegmentTravel(data, sol, fromRoute, left, left + len - 1);
      db newTravelA = sol.routeTravel[fromRoute] + deltaTravelA;
      db newDwellA = sol.routeDwell[fromRoute] - seg.dwellSum;
      db newTimeA = newTravelA + newDwellA;

      db oldCostA = data.routeCost(sol.routeTime[fromRoute], sol.routeLoad[fromRoute]);
      db newCostA = data.routeCost(newTimeA, newLoadA);

      int newLoadN = seg.loadSum;
      if (!enforceCapacity(data, newLoadN)) return false;

      db newTravelN = segInternal + edgeCost(data, segLast, 0);
      db newDwellN = seg.dwellSum;
      db newTimeN = newTravelN + newDwellN;
      db newCostN = data.routeCost(newTimeN, newLoadN);

      delta[0] = (newCostA - oldCostA) + newCostN;

      out.type = MoveType::OrOpt;
      out.delta = delta;
      out.payload = OrOptMove{fromRoute, left, len, toRoute, pos, reverseSeg};
      return true;
    }

    if (toRoute != fromRoute) {
      int newLoadA = sol.routeLoad[fromRoute] - seg.loadSum;
      int newLoadB = sol.routeLoad[toRoute] + seg.loadSum;
      if (!enforceCapacity(data, newLoadA) || !enforceCapacity(data, newLoadB)) return false;

      db deltaTravelA = deltaRemoveSegmentTravel(data, sol, fromRoute, left, left + len - 1);
      db deltaTravelB = deltaInsertSegmentTravel(data, sol, toRoute, pos, segFirst, segLast, segInternal);

      db newTravelA = sol.routeTravel[fromRoute] + deltaTravelA;
      db newTravelB = sol.routeTravel[toRoute] + deltaTravelB;

      db newDwellA = sol.routeDwell[fromRoute] - seg.dwellSum;
      db newDwellB = sol.routeDwell[toRoute] + seg.dwellSum;

      db newTimeA = newTravelA + newDwellA;
      db newTimeB = newTravelB + newDwellB;

      db oldCostA = data.routeCost(sol.routeTime[fromRoute], sol.routeLoad[fromRoute]);
      db oldCostB = data.routeCost(sol.routeTime[toRoute], sol.routeLoad[toRoute]);
      db newCostA = data.routeCost(newTimeA, newLoadA);
      db newCostB = data.routeCost(newTimeB, newLoadB);

      delta[0] = (newCostA - oldCostA) + (newCostB - oldCostB);

      out.type = MoveType::OrOpt;
      out.delta = delta;
      out.payload = OrOptMove{fromRoute, left, len, toRoute, pos, reverseSeg};
      return true;
    }

    // Intra-route Or-opt: remove seg then insert into after-removal at pos
    int sizeAfter = nA - len;
    // Remove delta on original
    db deltaRemove = deltaRemoveSegmentTravel(data, sol, fromRoute, left, left + len - 1);

    // Insertion delta into after-removal
    db deltaInsert = 0;
    if (sizeAfter == 0) {
      deltaInsert = segInternal + edgeCost(data, segLast, 0);
    } else if (pos == 0) {
      int next = stopAfterRemovalSeg(A, left, len, 0);
      deltaInsert = segInternal + edgeCost(data, segLast, next);
    } else if (pos == sizeAfter) {
      int prev = stopAfterRemovalSeg(A, left, len, sizeAfter - 1);
      deltaInsert = -edgeCost(data, prev, 0) + edgeCost(data, prev, segFirst) + segInternal + edgeCost(data, segLast, 0);
    } else {
      int prev = stopAfterRemovalSeg(A, left, len, pos - 1);
      int next = stopAfterRemovalSeg(A, left, len, pos);
      deltaInsert = -edgeCost(data, prev, next) + edgeCost(data, prev, segFirst) + segInternal + edgeCost(data, segLast, next);
    }

    db newTravel = sol.routeTravel[fromRoute] + deltaRemove + deltaInsert;
    db newTime = newTravel + sol.routeDwell[fromRoute];

    db oldCost = data.routeCost(sol.routeTime[fromRoute], sol.routeLoad[fromRoute]);
    db newCost = data.routeCost(newTime, sol.routeLoad[fromRoute]);
    delta[0] = newCost - oldCost;

    out.type = MoveType::OrOpt;
    out.delta = delta;
    out.payload = OrOptMove{fromRoute, left, len, toRoute, pos, reverseSeg};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<OrOptMove>(cand.payload);

    int fromRoute = mv.fromRoute;
    int toRoute = mv.toRoute;
    int left = mv.left;
    int len = mv.len;
    int pos = mv.pos;

    int R = (int)sol.routes.size();

    if (!validRouteIndex(sol, fromRoute)) return;
    if (!validRange(sol.routes[fromRoute], left, len)) return;
    if (toRoute != R && !validRouteIndex(sol, toRoute)) return;

    auto cutSegment = [&](Route& rt, int l, int ln, vector<int>& segS, vector<int>& segW) {
      int r = l + ln;
      segS.assign(rt.stops.begin() + l, rt.stops.begin() + r);
      segW.assign(rt.weight.begin() + l, rt.weight.begin() + r);
      rt.stops.erase(rt.stops.begin() + l, rt.stops.begin() + r);
      rt.weight.erase(rt.weight.begin() + l, rt.weight.begin() + r);
    };

    if (toRoute == R) {
      // create new route from segment
      auto& A = sol.routes[fromRoute];

      vector<int> segS, segW;
      cutSegment(A, left, len, segS, segW);

      if (mv.reverseSeg) {
        reverse(segS.begin(), segS.end());
        reverse(segW.begin(), segW.end());
      }

      Route nr;
      nr.stops = std::move(segS);
      nr.weight = std::move(segW);

      sol.routes.push_back(std::move(nr));


      cleanupEmptyRoutes(sol);
      rebuildAll(data, sol);
      return;
    }

    if (toRoute != fromRoute) {
      auto& A = sol.routes[fromRoute];
      auto& B = sol.routes[toRoute];

      vector<int> segS, segW;
      cutSegment(A, left, len, segS, segW);

      if (mv.reverseSeg) {
        reverse(segS.begin(), segS.end());
        reverse(segW.begin(), segW.end());
      }

      int p = min(max(pos, 0), (int)B.stops.size());
      B.stops.insert(B.stops.begin() + p, segS.begin(), segS.end());
      B.weight.insert(B.weight.begin() + p, segW.begin(), segW.end());


      cleanupEmptyRoutes(sol);
      rebuildAll(data, sol);
      return;
    }

    // intra-route: note pos is insertion index AFTER removal
    auto& A = sol.routes[fromRoute];

    vector<int> segS, segW;
    cutSegment(A, left, len, segS, segW);

    if (mv.reverseSeg) {
      reverse(segS.begin(), segS.end());
      reverse(segW.begin(), segW.end());
    }

    int p = min(max(pos, 0), (int)A.stops.size());
    A.stops.insert(A.stops.begin() + p, segS.begin(), segS.end());
    A.weight.insert(A.weight.begin() + p, segW.begin(), segW.end());

    rebuildAll(data, sol);
  }
};

// =======================
// (d.3) Reassign one address to another feasible stop, and repair route weights
// =======================
struct ReassignAddressOperator : MoveOperator {
  db w = 1.0;
  int maxAddrTries = 40;
  int maxRemovalCandidates = 12;
  int maxInsertRoutes = 6;
  int maxInsertPos = 6;

  string name() const override { return "ReassignAddress"; }
  db weight() const override { return w; }

  static db routeCostOf(const ProblemData& data, const Route& rt) {
    int n = (int)rt.stops.size();
    int load = 0;
    db dwellSum = 0;
    for (int i = 0; i < n; i++) {
      load += rt.weight[i];
      dwellSum += data.dwell(rt.weight[i]);
    }
    db travel = 0;
    if (n) {
      travel += data.driveTime[rt.stops.back()][0];
      for (int i = 1; i < n; i++) travel += data.driveTime[rt.stops[i - 1]][rt.stops[i]];
    }
    return data.routeCost(travel + dwellSum, load);
  }

  static int routeLoadOf(const Route& rt) {
    int load = 0;
    for (int w : rt.weight) load += w;
    return load;
  }

  static int findStopPos(const Route& rt, int stop) {
    for (int i = 0; i < (int)rt.stops.size(); i++) {
      if (rt.stops[i] == stop) return i;
    }
    return -1;
  }

  static bool applyRemoval(Route& rt, int pos, int w, bool& removedStop) {
    if (pos < 0 || pos >= (int)rt.stops.size()) return false;
    if (rt.weight[pos] < w) return false;
    if (rt.weight[pos] == w) {
      rt.stops.erase(rt.stops.begin() + pos);
      rt.weight.erase(rt.weight.begin() + pos);
      removedStop = true;
    } else {
      rt.weight[pos] -= w;
      removedStop = false;
    }
    return true;
  }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int A = data.addressCount;
    if (A <= 0 || (int)sol.assign.size() < A) return false;
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickAddr(0, A - 1);
    int address = -1;
    int oldStop = -1;
    int newStop = -1;
    int wPassengers = 0;

    for (int tries = 0; tries < maxAddrTries; tries++) {
      int a = pickAddr(rng);
      if (a < 0 || a >= (int)sol.assign.size()) continue;
      int w = data.passengers[a];
      if (w <= 0) continue;
      if (data.P.hardCapacity && w > data.P.capacity) continue;

      const auto& opts = data.walkOptions[a];
      if ((int)opts.size() < 2) continue;

      int sOld = sol.assign[a];
      int pick = -1;
      if (!opts.empty()) {
        uniform_int_distribution<int> pickOpt(0, (int)opts.size() - 1);
        for (int t = 0; t < 6; t++) {
          int idx = pickOpt(rng);
          if (opts[idx].stop != sOld) { pick = idx; break; }
        }
        if (pick == -1) {
          for (int idx = 0; idx < (int)opts.size(); idx++) {
            if (opts[idx].stop != sOld) { pick = idx; break; }
          }
        }
      }
      if (pick == -1) continue;

      address = a;
      oldStop = sOld;
      newStop = opts[pick].stop;
      wPassengers = w;
      break;
    }

    if (address == -1) return false;

    vector<pair<int, int>> oldOcc;
    oldOcc.reserve(8);
    unordered_map<int, int> newPos;
    newPos.reserve(R * 2 + 1);

    for (int r = 0; r < R; r++) {
      const auto& rt = sol.routes[r];
      for (int i = 0; i < (int)rt.stops.size(); i++) {
        if (rt.stops[i] == oldStop && rt.weight[i] >= wPassengers) oldOcc.push_back({r, i});
        if (rt.stops[i] == newStop && !newPos.count(r)) newPos[r] = i;
      }
    }

    if (oldOcc.empty()) return false;
    if ((int)oldOcc.size() > maxRemovalCandidates) {
      shuffle(oldOcc.begin(), oldOcc.end(), rng);
      oldOcc.resize(maxRemovalCandidates);
    }

    bool hasBest = false;
    db bestDelta = 0;
    ReassignAddressMove bestMove;

    auto consider = [&](db delta, const ReassignAddressMove& mv) {
      if (!hasBest || delta + EPS < bestDelta) {
        hasBest = true;
        bestDelta = delta;
        bestMove = mv;
      }
    };

    for (auto [rRem, posRem] : oldOcc) {
      Route removed = sol.routes[rRem];
      bool removedStop = false;
      if (!applyRemoval(removed, posRem, wPassengers, removedStop)) continue;

      db oldCostRem = data.routeCost(sol.routeTime[rRem], sol.routeLoad[rRem]);
      db newCostRem = routeCostOf(data, removed);
      db baseDelta = newCostRem - oldCostRem;

      // Add to existing stop in the same route (after removal).
      int posSame = findStopPos(removed, newStop);
      if (posSame != -1) {
        int load = routeLoadOf(removed);
        if (!data.P.hardCapacity || load + wPassengers <= data.P.capacity) {
          Route added = removed;
          added.weight[posSame] += wPassengers;
          db newCost = routeCostOf(data, added);
          ReassignAddressMove mv;
          mv.address = address;
          mv.oldStop = oldStop;
          mv.newStop = newStop;
          mv.removeRoute = rRem;
          mv.removePos = posRem;
          mv.removeStop = removedStop;
          mv.addRoute = rRem;
          mv.addPos = posSame;
          mv.addExisting = true;
          consider(newCost - oldCostRem, mv);
        }
      }

      // Add to existing stop in other routes.
      for (auto& it : newPos) {
        int rAdd = it.first;
        int posAdd = it.second;
        if (rAdd == rRem) continue;
        if (data.P.hardCapacity && sol.routeLoad[rAdd] + wPassengers > data.P.capacity) continue;

        Route added = sol.routes[rAdd];
        if (posAdd < 0 || posAdd >= (int)added.stops.size()) continue;
        added.weight[posAdd] += wPassengers;

        db oldCostAdd = data.routeCost(sol.routeTime[rAdd], sol.routeLoad[rAdd]);
        db newCostAdd = routeCostOf(data, added);

        ReassignAddressMove mv;
        mv.address = address;
        mv.oldStop = oldStop;
        mv.newStop = newStop;
        mv.removeRoute = rRem;
        mv.removePos = posRem;
        mv.removeStop = removedStop;
        mv.addRoute = rAdd;
        mv.addPos = posAdd;
        mv.addExisting = true;
        consider(baseDelta + (newCostAdd - oldCostAdd), mv);
      }

      // Insert new stop into selected routes (skip routes that already have newStop).
      unordered_set<int> routesToTry;
      routesToTry.reserve((size_t)maxInsertRoutes + 1);
      routesToTry.insert(rRem);

      uniform_int_distribution<int> pickRoute(0, R - 1);
      for (int t = 0; t < maxInsertRoutes; t++) {
        routesToTry.insert(pickRoute(rng));
      }

      for (int rAdd : routesToTry) {
        const Route* base = nullptr;
        if (rAdd == rRem) {
          if (posSame != -1) continue;
          base = &removed;
        } else {
          if (newPos.count(rAdd)) continue;
          base = &sol.routes[rAdd];
        }

        int load = routeLoadOf(*base);
        if (data.P.hardCapacity && load + wPassengers > data.P.capacity) continue;

        int n = (int)base->stops.size();
        int posTries = min(maxInsertPos, n + 1);
        if (n == 0) posTries = 1;

        unordered_set<int> usedPos;
        usedPos.reserve((size_t)posTries * 2);
        uniform_int_distribution<int> pickPos(0, max(0, n));

        for (int t = 0; t < posTries; t++) {
          int pos = (n == 0 ? 0 : pickPos(rng));
          if (!usedPos.insert(pos).second) continue;

          Route added = *base;
          added.stops.insert(added.stops.begin() + pos, newStop);
          added.weight.insert(added.weight.begin() + pos, wPassengers);

          db newCostAdd = routeCostOf(data, added);

          ReassignAddressMove mv;
          mv.address = address;
          mv.oldStop = oldStop;
          mv.newStop = newStop;
          mv.removeRoute = rRem;
          mv.removePos = posRem;
          mv.removeStop = removedStop;
          mv.addRoute = rAdd;
          mv.addPos = pos;
          mv.addExisting = false;

          if (rAdd == rRem) {
            consider(newCostAdd - oldCostRem, mv);
          } else {
            db oldCostAdd = data.routeCost(sol.routeTime[rAdd], sol.routeLoad[rAdd]);
            consider(baseDelta + (newCostAdd - oldCostAdd), mv);
          }
        }
      }

      // Create a new route for newStop.
      if (!data.P.hardCapacity || wPassengers <= data.P.capacity) {
        Route nr;
        nr.stops.push_back(newStop);
        nr.weight.push_back(wPassengers);
        db newCost = routeCostOf(data, nr);

        ReassignAddressMove mv;
        mv.address = address;
        mv.oldStop = oldStop;
        mv.newStop = newStop;
        mv.removeRoute = rRem;
        mv.removePos = posRem;
        mv.removeStop = removedStop;
        mv.addRoute = -1;
        mv.addPos = 0;
        mv.addExisting = false;
        consider(baseDelta + newCost, mv);
      }
    }

    if (!hasBest) return false;

    out.type = MoveType::ReassignAddress;
    out.delta = vector<db>{bestDelta};
    out.payload = bestMove;
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<ReassignAddressMove>(cand.payload);

    if (mv.address < 0 || mv.address >= (int)sol.assign.size()) return;
    int wPassengers = data.passengers[mv.address];
    if (wPassengers <= 0) return;
    if (!validRouteIndex(sol, mv.removeRoute)) return;

    auto& remRoute = sol.routes[mv.removeRoute];
    if (!validPos(remRoute, mv.removePos)) return;
    if (remRoute.stops[mv.removePos] != mv.oldStop) return;
    if (remRoute.weight[mv.removePos] < wPassengers) return;

    int sizeAfter = (int)remRoute.stops.size() - (remRoute.weight[mv.removePos] == wPassengers ? 1 : 0);

    if (mv.addRoute != -1) {
      if (!validRouteIndex(sol, mv.addRoute)) return;
      if (mv.addRoute == mv.removeRoute) {
        if (mv.addExisting) {
          if (mv.addPos < 0 || mv.addPos >= sizeAfter) return;
        } else {
          if (mv.addPos < 0 || mv.addPos > sizeAfter) return;
        }
      } else {
        auto& addRoute = sol.routes[mv.addRoute];
        if (mv.addExisting) {
          if (!validPos(addRoute, mv.addPos)) return;
        } else {
          if (!validInsertPos(addRoute, mv.addPos)) return;
        }
      }
    }

    // Apply removal.
    if (remRoute.weight[mv.removePos] == wPassengers) {
      remRoute.stops.erase(remRoute.stops.begin() + mv.removePos);
      remRoute.weight.erase(remRoute.weight.begin() + mv.removePos);
    } else {
      remRoute.weight[mv.removePos] -= wPassengers;
      if (remRoute.weight[mv.removePos] == 0) {
        remRoute.stops.erase(remRoute.stops.begin() + mv.removePos);
        remRoute.weight.erase(remRoute.weight.begin() + mv.removePos);
      }
    }

    // Apply addition.
    if (mv.addRoute == -1) {
      Route nr;
      nr.stops.push_back(mv.newStop);
      nr.weight.push_back(wPassengers);
      sol.routes.push_back(std::move(nr));
    } else {
      auto& addRoute = sol.routes[mv.addRoute];
      if (mv.addExisting) {
        int pos = mv.addPos;
        if (!validPos(addRoute, pos) || addRoute.stops[pos] != mv.newStop) {
          int fallback = findStopPos(addRoute, mv.newStop);
          if (fallback == -1) {
            addRoute.stops.push_back(mv.newStop);
            addRoute.weight.push_back(wPassengers);
          } else {
            addRoute.weight[fallback] += wPassengers;
          }
        } else {
          addRoute.weight[pos] += wPassengers;
        }
      } else {
        int pos = min(max(mv.addPos, 0), (int)addRoute.stops.size());
        addRoute.stops.insert(addRoute.stops.begin() + pos, mv.newStop);
        addRoute.weight.insert(addRoute.weight.begin() + pos, wPassengers);
      }
    }

    sol.assign[mv.address] = mv.newStop;

    cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
  }
};

// =======================
// (d.4) Merge all addresses from one stop into another feasible stop
// =======================
struct StopMergeOperator : MoveOperator {
  db w = 0.8;
  int maxStopTries = 30;
  int maxStopCandidates = 6;
  int maxInsertRoutes = 8;
  int maxInsertPos = 8;

  string name() const override { return "StopMerge"; }
  db weight() const override { return w; }

  static db routeCostOf(const ProblemData& data, const Route& rt) {
    int n = (int)rt.stops.size();
    int load = 0;
    db dwellSum = 0;
    for (int i = 0; i < n; i++) {
      load += rt.weight[i];
      dwellSum += data.dwell(rt.weight[i]);
    }
    db travel = 0;
    if (n) {
      travel += data.driveTime[rt.stops.back()][0];
      for (int i = 1; i < n; i++) travel += data.driveTime[rt.stops[i - 1]][rt.stops[i]];
    }
    return data.routeCost(travel + dwellSum, load);
  }

  static int routeLoadOf(const Route& rt) {
    int load = 0;
    for (int w : rt.weight) load += w;
    return load;
  }

  static int findStopPos(const Route& rt, int stop) {
    for (int i = 0; i < (int)rt.stops.size(); i++) {
      if (rt.stops[i] == stop) return i;
    }
    return -1;
  }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int A = data.addressCount;
    int R = (int)sol.routes.size();
    if (A <= 0 || R == 0) return false;
    if ((int)sol.assign.size() < A) return false;

    vector<char> usedStop(data.stopCount, 0);
    for (const auto& rt : sol.routes) {
      for (int s : rt.stops) {
        if (0 <= s && s < data.stopCount) usedStop[s] = 1;
      }
    }

    uniform_int_distribution<int> pickAddr(0, A - 1);

    for (int tries = 0; tries < maxStopTries; tries++) {
      int a = pickAddr(rng);
      int oldStop = (0 <= a && a < (int)sol.assign.size()) ? sol.assign[a] : -1;
      if (oldStop < 0 || oldStop >= data.stopCount) continue;
      if (!usedStop[oldStop]) continue;

      vector<int> addrList;
      addrList.reserve(16);
      ll totalPassengers = 0;
      for (int i = 0; i < A; i++) {
        if (sol.assign[i] == oldStop) {
          addrList.push_back(i);
          totalPassengers += data.passengers[i];
        }
      }
      if (addrList.empty() || totalPassengers <= 0) continue;
      if (data.P.hardCapacity && totalPassengers > data.P.capacity) continue;

      vector<int> count(data.stopCount, 0);
      vector<char> seen(data.stopCount, 0);
      for (int addr : addrList) {
        fill(seen.begin(), seen.end(), 0);
        for (const auto& opt : data.walkOptions[addr]) {
          if (opt.dist > data.P.maxWalkDistance + EPS) continue;
          if (0 <= opt.stop && opt.stop < data.stopCount && !seen[opt.stop]) {
            count[opt.stop]++;
            seen[opt.stop] = 1;
          }
        }
      }

      vector<int> candidates;
      candidates.reserve(32);
      for (int s = 0; s < data.stopCount; s++) {
        if (s == oldStop) continue;
        if (count[s] == (int)addrList.size()) candidates.push_back(s);
      }
      if (candidates.empty()) continue;

      ll totalWeight = 0;
      vector<int> hasOldRoute;
      hasOldRoute.reserve(R);
      for (int r = 0; r < R; r++) {
        bool hasOld = false;
        for (int i = 0; i < (int)sol.routes[r].stops.size(); i++) {
          if (sol.routes[r].stops[i] == oldStop) {
            totalWeight += sol.routes[r].weight[i];
            hasOld = true;
          }
        }
        if (hasOld) hasOldRoute.push_back(r);
      }
      if (totalWeight != totalPassengers) continue;

      db baseDelta = 0;
      unordered_map<int, Route> removedRoutes;
      unordered_map<int, db> removedCost;
      unordered_map<int, db> baseCost;
      removedRoutes.reserve(hasOldRoute.size() * 2 + 1);
      removedCost.reserve(hasOldRoute.size() * 2 + 1);
      baseCost.reserve(R * 2 + 1);

      for (int r : hasOldRoute) {
        const auto& rt = sol.routes[r];
        Route nr;
        nr.stops.reserve(rt.stops.size());
        nr.weight.reserve(rt.weight.size());
        for (int i = 0; i < (int)rt.stops.size(); i++) {
          if (rt.stops[i] == oldStop) continue;
          nr.stops.push_back(rt.stops[i]);
          nr.weight.push_back(rt.weight[i]);
        }
        db oldCost = data.routeCost(sol.routeTime[r], sol.routeLoad[r]);
        db newCost = routeCostOf(data, nr);
        baseDelta += newCost - oldCost;
        removedRoutes[r] = std::move(nr);
        removedCost[r] = newCost;
      }

      for (int r = 0; r < R; r++) {
        if (removedRoutes.count(r)) {
          baseCost[r] = removedCost[r];
        } else {
          baseCost[r] = data.routeCost(sol.routeTime[r], sol.routeLoad[r]);
        }
      }

      shuffle(candidates.begin(), candidates.end(), rng);
      int limit = min(maxStopCandidates, (int)candidates.size());

      bool hasBest = false;
      db bestDelta = 0;
      StopMergeMove bestMove;

      for (int idx = 0; idx < limit; idx++) {
        int newStop = candidates[idx];

        auto consider = [&](db delta, int r, int pos, bool addExisting) {
          if (!hasBest || delta + EPS < bestDelta) {
            hasBest = true;
            bestDelta = delta;
            bestMove.oldStop = oldStop;
            bestMove.newStop = newStop;
            bestMove.addRoute = r;
            bestMove.addPos = pos;
            bestMove.addExisting = addExisting;
          }
        };

        // Add to existing stop in a route (if present).
        for (int r = 0; r < R; r++) {
          const Route* base = removedRoutes.count(r) ? &removedRoutes[r] : &sol.routes[r];
          int pos = findStopPos(*base, newStop);
          if (pos == -1) continue;

          int load = routeLoadOf(*base);
          if (data.P.hardCapacity && load + totalPassengers > data.P.capacity) continue;

          Route added = *base;
          added.weight[pos] += (int)totalPassengers;
          db newCost = routeCostOf(data, added);
          db delta = baseDelta + (newCost - baseCost[r]);
          consider(delta, r, pos, true);
        }

        // Insert new stop into a subset of routes (if not already present).
        unordered_set<int> routesToTry;
        routesToTry.reserve((size_t)maxInsertRoutes + 1);
        uniform_int_distribution<int> pickRoute(0, R - 1);
        for (int t = 0; t < maxInsertRoutes; t++) routesToTry.insert(pickRoute(rng));
        routesToTry.insert(0);

        for (int r : routesToTry) {
          const Route* base = removedRoutes.count(r) ? &removedRoutes[r] : &sol.routes[r];
          if (findStopPos(*base, newStop) != -1) continue;

          int load = routeLoadOf(*base);
          if (data.P.hardCapacity && load + totalPassengers > data.P.capacity) continue;

          int n = (int)base->stops.size();
          if (n == 0) {
            Route added = *base;
            added.stops.push_back(newStop);
            added.weight.push_back((int)totalPassengers);
            db newCost = routeCostOf(data, added);
            db delta = baseDelta + (newCost - baseCost[r]);
            consider(delta, r, 0, false);
            continue;
          }

          unordered_set<int> usedPos;
          usedPos.reserve((size_t)maxInsertPos * 2 + 1);
          uniform_int_distribution<int> pickPos(0, n);
          for (int t = 0; t < maxInsertPos; t++) {
            int pos = pickPos(rng);
            if (!usedPos.insert(pos).second) continue;
            Route added = *base;
            added.stops.insert(added.stops.begin() + pos, newStop);
            added.weight.insert(added.weight.begin() + pos, (int)totalPassengers);
            db newCost = routeCostOf(data, added);
            db delta = baseDelta + (newCost - baseCost[r]);
            consider(delta, r, pos, false);
          }
        }

        // New route option.
        if (!data.P.hardCapacity || totalPassengers <= data.P.capacity) {
          Route nr;
          nr.stops.push_back(newStop);
          nr.weight.push_back((int)totalPassengers);
          db newCost = routeCostOf(data, nr);
          consider(baseDelta + newCost, -1, 0, false);
        }
      }

      if (!hasBest) continue;

      out.type = MoveType::StopMerge;
      out.delta = vector<db>{bestDelta};
      out.payload = bestMove;
      return true;
    }

    return false;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<StopMergeMove>(cand.payload);
    if (mv.oldStop < 0 || mv.oldStop >= data.stopCount) return;
    if (mv.newStop < 0 || mv.newStop >= data.stopCount) return;
    if (mv.addRoute != -1 && !validRouteIndex(sol, mv.addRoute)) return;

    ll totalPassengers = 0;
    for (int i = 0; i < (int)sol.assign.size(); i++) {
      if (sol.assign[i] == mv.oldStop) totalPassengers += data.passengers[i];
    }
    if (totalPassengers <= 0) return;
    if (data.P.hardCapacity && totalPassengers > data.P.capacity) return;

    ll totalWeight = 0;
    for (const auto& rt : sol.routes) {
      for (int i = 0; i < (int)rt.stops.size(); i++) {
        if (rt.stops[i] == mv.oldStop) totalWeight += rt.weight[i];
      }
    }
    if (totalWeight != totalPassengers) return;

    for (auto& rt : sol.routes) {
      for (int i = 0; i < (int)rt.stops.size(); i++) {
        if (rt.stops[i] == mv.oldStop) {
          rt.stops.erase(rt.stops.begin() + i);
          rt.weight.erase(rt.weight.begin() + i);
          i--;
        }
      }
    }

    if (mv.addRoute == -1) {
      Route nr;
      nr.stops.push_back(mv.newStop);
      nr.weight.push_back((int)totalPassengers);
      sol.routes.push_back(std::move(nr));
    } else {
      auto& addRoute = sol.routes[mv.addRoute];

      int load = 0;
      for (int w : addRoute.weight) load += w;
      if (data.P.hardCapacity && load + totalPassengers > data.P.capacity) return;

      if (mv.addExisting) {
        int pos = (0 <= mv.addPos && mv.addPos < (int)addRoute.stops.size()) ? mv.addPos : -1;
        if (pos == -1 || addRoute.stops[pos] != mv.newStop) pos = findStopPos(addRoute, mv.newStop);
        if (pos == -1) {
          int ins = min(max(mv.addPos, 0), (int)addRoute.stops.size());
          addRoute.stops.insert(addRoute.stops.begin() + ins, mv.newStop);
          addRoute.weight.insert(addRoute.weight.begin() + ins, (int)totalPassengers);
        } else {
          addRoute.weight[pos] += (int)totalPassengers;
        }
      } else {
        int pos = min(max(mv.addPos, 0), (int)addRoute.stops.size());
        if (pos < (int)addRoute.stops.size() && addRoute.stops[pos] == mv.newStop) {
          addRoute.weight[pos] += (int)totalPassengers;
        } else {
          int existing = findStopPos(addRoute, mv.newStop);
          if (existing != -1) {
            addRoute.weight[existing] += (int)totalPassengers;
          } else {
            addRoute.stops.insert(addRoute.stops.begin() + pos, mv.newStop);
            addRoute.weight.insert(addRoute.weight.begin() + pos, (int)totalPassengers);
          }
        }
      }
    }

    for (int i = 0; i < (int)sol.assign.size(); i++) {
      if (sol.assign[i] == mv.oldStop) sol.assign[i] = mv.newStop;
    }

    cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
  }
};

// =======================
// (d.5) Split route: cut a route into two routes
// =======================
struct SplitRouteOperator : MoveOperator {
  db w = 0.6;
  string name() const override { return "SplitRoute"; }
  db weight() const override { return w; }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);
    int r = -1;
    for (int tries = 0; tries < 30; tries++) {
      int rr = pickRoute(rng);
      if ((int)sol.routes[rr].stops.size() >= 2) { r = rr; break; }
    }
    if (r == -1) return false;

    const auto& route = sol.routes[r];
    int n = (int)route.stops.size();

    uniform_int_distribution<int> pickCut(0, n - 2); // prefix [0..cut], suffix [cut+1..n-1]
    int cut = pickCut(rng);

    const auto& cache = sol.cache[r];
    int loadA = cache.segmentLoad(0, cut);
    int loadB = sol.routeLoad[r] - loadA;

    if (!enforceCapacity(data, loadA) || !enforceCapacity(data, loadB)) return false;

    db dwellA = cache.segmentDwell(0, cut);
    db dwellB = cache.segmentDwell(cut + 1, n - 1);

    int lastA = route.stops[cut];
    int lastB = route.stops[n - 1];

    db travelA = cache.segmentForward(0, cut) + edgeCost(data, lastA, 0);
    db travelB = cache.segmentForward(cut + 1, n - 1) + edgeCost(data, lastB, 0);

    db costOld = data.routeCost(sol.routeTime[r], sol.routeLoad[r]);
    db costNew = data.routeCost(travelA + dwellA, loadA) + data.routeCost(travelB + dwellB, loadB);

    vector<db> delta = { costNew - costOld };

    out.type = MoveType::SplitRoute;
    out.delta = delta;
    out.payload = SplitRouteMove{r, cut};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<SplitRouteMove>(cand.payload);
    int r = mv.route;
    int cut = mv.cut;

    if (!validRouteIndex(sol, r)) return;
    auto& route = sol.routes[r];
    int n = (int)route.stops.size();
    if (n < 2) return;
    if (cut < 0 || cut >= n - 1) return;

    Route nr;
    nr.stops.assign(route.stops.begin() + cut + 1, route.stops.end());
    nr.weight.assign(route.weight.begin() + cut + 1, route.weight.end());

    route.stops.erase(route.stops.begin() + cut + 1, route.stops.end());
    route.weight.erase(route.weight.begin() + cut + 1, route.weight.end());

    sol.routes.push_back(std::move(nr));

    cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
  }
};

// =======================
// (e) Three-opt within a route
// We keep start fixed (no depot->first edge in your model), so we only rearrange segments after 3 cuts.
// Segments: A = [0..a], B=[a+1..b], C=[b+1..c], D=[c+1..n-1] (D may be empty).
// Patterns (1..7) we test:
// 1: A rev(B) C D
// 2: A B rev(C) D
// 3: A rev(B) rev(C) D
// 4: A C B D
// 5: A rev(C) B D
// 6: A C rev(B) D
// 7: A rev(C) rev(B) D
// =======================
struct ThreeOptOperator : MoveOperator {
  db w = 1.0;
  string name() const override { return "ThreeOpt"; }
  db weight() const override { return w; }

  struct Part { SegmentInfo seg; bool rev = false; bool empty = false; };

  static int segFirst(const Part& p) { return p.empty ? -1 : (p.rev ? p.seg.lastStop : p.seg.firstStop); }
  static int segLast(const Part& p)  { return p.empty ? -1 : (p.rev ? p.seg.firstStop : p.seg.lastStop); }
  static db segInternal(const Part& p) { return p.empty ? 0 : (p.rev ? p.seg.internalReverse : p.seg.internalForward); }

  static db concatTravel(const ProblemData& data, const vector<Part>& parts) {
    // route travel = sum internal + sum connect(last_i, first_{i+1}) + last->0
    int lastNode = -1;
    db total = 0;
    bool hasAny = false;

    for (const auto& p : parts) {
      if (p.empty) continue;
      int f = segFirst(p);
      int l = segLast(p);
      if (!hasAny) {
        // first segment: no depot->first edge in this model
        hasAny = true;
      } else {
        total += edgeCost(data, lastNode, f);
      }
      total += segInternal(p);
      lastNode = l;
    }

    if (!hasAny) return 0;
    total += edgeCost(data, lastNode, 0);
    return total;
  }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);

    int r = -1;
    for (int tries = 0; tries < 30; tries++) {
      int rr = pickRoute(rng);
      if ((int)sol.routes[rr].stops.size() >= 4) { r = rr; break; }
    }
    if (r == -1) return false;

    int n = (int)sol.routes[r].stops.size();

    // choose cut AFTER a, AFTER b, AFTER c
    uniform_int_distribution<int> pickA(0, n - 3);
    int a = pickA(rng);

    uniform_int_distribution<int> pickB(a + 1, n - 2);
    int b = pickB(rng);

    uniform_int_distribution<int> pickC(b + 1, n - 1);
    int c = pickC(rng);

    // segments
    SegmentInfo A = getSegmentInfo(data, sol, r, 0, a + 1);
    SegmentInfo B = getSegmentInfo(data, sol, r, a + 1, b - a);
    SegmentInfo C = getSegmentInfo(data, sol, r, b + 1, c - b);

    Part pA{A, false, false};
    Part pB{B, false, false};
    Part pC{C, false, false};

    Part pD;
    if (c + 1 <= n - 1) {
      SegmentInfo D = getSegmentInfo(data, sol, r, c + 1, n - (c + 1));
      pD = Part{D, false, false};
    } else {
      pD = Part{};
      pD.empty = true;
    }

    db oldTravel = sol.routeTravel[r];
    db oldDwell = sol.routeDwell[r];
    int oldLoad = sol.routeLoad[r];
    db oldCost = data.routeCost(sol.routeTime[r], oldLoad);

    int bestPattern = -1;
    db bestNewTravel = 0;

    for (int pat = 1; pat <= 7; pat++) {
      vector<Part> parts;
      parts.reserve(4);

      Part qA = pA, qB = pB, qC = pC, qD = pD;

      if (pat == 1) { qB.rev = true; parts = {qA, qB, qC, qD}; }
      if (pat == 2) { qC.rev = true; parts = {qA, qB, qC, qD}; }
      if (pat == 3) { qB.rev = true; qC.rev = true; parts = {qA, qB, qC, qD}; }
      if (pat == 4) { parts = {qA, qC, qB, qD}; }
      if (pat == 5) { qC.rev = true; parts = {qA, qC, qB, qD}; }
      if (pat == 6) { qB.rev = true; parts = {qA, qC, qB, qD}; /* note: qB.rev means reverse(B) after swap */ }
      if (pat == 7) { qB.rev = true; qC.rev = true; parts = {qA, qC, qB, qD}; }

      db newTravel = concatTravel(data, parts);
      db newTime = newTravel + oldDwell;
      db newCost = data.routeCost(newTime, oldLoad);

      if (bestPattern == -1 || newCost + EPS < data.routeCost(bestNewTravel + oldDwell, oldLoad)) {
        bestPattern = pat;
        bestNewTravel = newTravel;
      }
    }

    if (bestPattern == -1) return false;

    db newTime = bestNewTravel + oldDwell;
    db newCost = data.routeCost(newTime, oldLoad);

    vector<db> delta = { newCost - oldCost };

    out.type = MoveType::ThreeOpt;
    out.delta = delta;
    out.payload = ThreeOptMove{r, a, b, c, bestPattern};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<ThreeOptMove>(cand.payload);
    int r = mv.route;
    if (!validRouteIndex(sol, r)) return;
    auto& route = sol.routes[r];

    int a = mv.a, b = mv.b, c = mv.c;
    if (a < 0 || b <= a || c <= b || c >= (int)route.stops.size()) return;

    // Extract segments
    auto slice = [&](int l, int rr, vector<int>& s, vector<int>& w) {
      if (l > rr) { s.clear(); w.clear(); return; }
      s.assign(route.stops.begin() + l, route.stops.begin() + rr + 1);
      w.assign(route.weight.begin() + l, route.weight.begin() + rr + 1);
    };

    vector<int> As, Bs, Cs, Ds;
    vector<int> Aw, Bw, Cw, Dw;

    slice(0, a, As, Aw);
    slice(a + 1, b, Bs, Bw);
    slice(b + 1, c, Cs, Cw);
    slice(c + 1, (int)route.stops.size() - 1, Ds, Dw);

    auto rev = [&](vector<int>& s, vector<int>& w) {
      reverse(s.begin(), s.end());
      reverse(w.begin(), w.end());
    };

    // Build new
    vector<int> ns, nw;
    auto append = [&](const vector<int>& s, const vector<int>& w) {
      ns.insert(ns.end(), s.begin(), s.end());
      nw.insert(nw.end(), w.begin(), w.end());
    };

    int pat = mv.pattern;

    // Prepare copies with possible reversals
    vector<int> Bs2 = Bs, Bw2 = Bw;
    vector<int> Cs2 = Cs, Cw2 = Cw;

    if (pat == 1) rev(Bs2, Bw2);
    if (pat == 2) rev(Cs2, Cw2);
    if (pat == 3) { rev(Bs2, Bw2); rev(Cs2, Cw2); }
    if (pat == 5) rev(Cs2, Cw2);
    if (pat == 6) rev(Bs2, Bw2);
    if (pat == 7) { rev(Bs2, Bw2); rev(Cs2, Cw2); }

    append(As, Aw);
    if (pat <= 3) {
      append(Bs2, Bw2);
      append(Cs2, Cw2);
    } else {
      // swapped order C then B
      append(Cs2, Cw2);
      append(Bs2, Bw2);
    }
    append(Ds, Dw);

    route.stops.swap(ns);
    route.weight.swap(nw);

    rebuildAll(data, sol);
  }
};

// =======================
// (f) Three-point: swap adjacent pair with a third node (can be inter-route)
// Implemented as a restricted cross-exchange: lenA=2, lenB=1, optional reverse of the pair when inserted.
// =======================
struct ThreePointOperator : MoveOperator {
  db w = 1.0;
  db pReversePair = 0.25;

  string name() const override { return "ThreePoint"; }
  db weight() const override { return w; }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int R = (int)sol.routes.size();
    if (R == 0) return false;

    uniform_int_distribution<int> pickRoute(0, R - 1);

    int rPair = -1;
    for (int tries = 0; tries < 50; tries++) {
      int r = pickRoute(rng);
      if ((int)sol.routes[r].stops.size() >= 2) { rPair = r; break; }
    }
    if (rPair == -1) return false;

    int rSingle = -1;
    for (int tries = 0; tries < 50; tries++) {
      int r = pickRoute(rng);
      if (r == rPair) continue;
      if (!sol.routes[r].stops.empty()) { rSingle = r; break; }
    }
    if (rSingle == -1) return false;

    const auto& A = sol.routes[rPair];
    const auto& B = sol.routes[rSingle];

    uniform_int_distribution<int> pickPosPair(0, (int)A.stops.size() - 2);
    int posPair = pickPosPair(rng);

    uniform_int_distribution<int> pickPosSingle(0, (int)B.stops.size() - 1);
    int posSingle = pickPosSingle(rng);

    // rPair != rSingle by construction

    bool reversePair = (uniform_real_distribution<db>(0, 1)(rng) < pReversePair);

    auto segPair = getSegmentInfo(data, sol, rPair, posPair, 2);
    auto segOne = getSegmentInfo(data, sol, rSingle, posSingle, 1);

    int newLoadA = sol.routeLoad[rPair] - segPair.loadSum + segOne.loadSum;
    int newLoadB = sol.routeLoad[rSingle] - segOne.loadSum + segPair.loadSum;
    if (!enforceCapacity(data, newLoadA) || !enforceCapacity(data, newLoadB)) return false;

    // Travel deltas: replace each segment with the other
    db deltaTravelA = deltaReplaceSegmentTravel(data, sol, rPair, posPair, posPair + 1, segOne, false);
    db deltaTravelB = deltaReplaceSegmentTravel(data, sol, rSingle, posSingle, posSingle, segPair, reversePair);

    db newTravelA = sol.routeTravel[rPair] + deltaTravelA;
    db newTravelB = sol.routeTravel[rSingle] + deltaTravelB;

    db newDwellA = sol.routeDwell[rPair] - segPair.dwellSum + segOne.dwellSum;
    db newDwellB = sol.routeDwell[rSingle] - segOne.dwellSum + segPair.dwellSum;

    db newTimeA = newTravelA + newDwellA;
    db newTimeB = newTravelB + newDwellB;

    db oldCostA = data.routeCost(sol.routeTime[rPair], sol.routeLoad[rPair]);
    db oldCostB = data.routeCost(sol.routeTime[rSingle], sol.routeLoad[rSingle]);

    db newCostA = data.routeCost(newTimeA, newLoadA);
    db newCostB = data.routeCost(newTimeB, newLoadB);

    vector<db> delta = { (newCostA - oldCostA) + (newCostB - oldCostB) };

    out.type = MoveType::ThreePoint;
    out.delta = delta;
    out.payload = ThreePointMove{rPair, posPair, rSingle, posSingle, reversePair};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<ThreePointMove>(cand.payload);

    int rA = mv.rPair;
    int rB = mv.rSingle;
    int leftA = mv.posPair;
    int leftB = mv.posSingle;

    if (!validRouteIndex(sol, rA) || !validRouteIndex(sol, rB)) return;
    if (rA == rB) return;
    auto& A = sol.routes[rA];
    auto& B = sol.routes[rB];

    if (leftA < 0 || leftA + 1 >= (int)A.stops.size()) return;
    if (!validPos(B, leftB)) return;

    vector<int> segAStops(A.stops.begin() + leftA, A.stops.begin() + leftA + 2);
    vector<int> segAWeight(A.weight.begin() + leftA, A.weight.begin() + leftA + 2);

    vector<int> segBStops(B.stops.begin() + leftB, B.stops.begin() + leftB + 1);
    vector<int> segBWeight(B.weight.begin() + leftB, B.weight.begin() + leftB + 1);

    // erase
    A.stops.erase(A.stops.begin() + leftA, A.stops.begin() + leftA + 2);
    A.weight.erase(A.weight.begin() + leftA, A.weight.begin() + leftA + 2);

    B.stops.erase(B.stops.begin() + leftB, B.stops.begin() + leftB + 1);
    B.weight.erase(B.weight.begin() + leftB, B.weight.begin() + leftB + 1);

    // insert swapped
    A.stops.insert(A.stops.begin() + leftA, segBStops.begin(), segBStops.end());
    A.weight.insert(A.weight.begin() + leftA, segBWeight.begin(), segBWeight.end());

    if (mv.reversePair) {
      reverse(segAStops.begin(), segAStops.end());
      reverse(segAWeight.begin(), segAWeight.end());
    }
    B.stops.insert(B.stops.begin() + leftB, segAStops.begin(), segAStops.end());
    B.weight.insert(B.weight.begin() + leftB, segAWeight.begin(), segAWeight.end());


    cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
  }
};

// =======================
// (g) Cross-exchange: swap segments (len 1..4) between routes, allow reversals
// =======================
struct CrossExchangeOperator : MoveOperator {
  db w = 1.0;
  int minLen = 1;
  int maxLen = 4;

  string name() const override { return "CrossExchange"; }
  db weight() const override { return w; }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    int routeCount = (int)sol.routes.size();
    if (routeCount < 2) return false;

    uniform_int_distribution<int> pickRoute(0, routeCount - 1);

    int a = -1, b = -1;
    for (int tries = 0; tries < 50; tries++) {
      int ra = pickRoute(rng);
      int rb = pickRoute(rng);
      if (ra == rb) continue;
      if (sol.routes[ra].stops.empty() || sol.routes[rb].stops.empty()) continue;
      a = ra; b = rb;
      break;
    }
    if (a == -1) return false;

    const auto& A = sol.routes[a];
    const auto& B = sol.routes[b];

    int nA = (int)A.stops.size();
    int nB = (int)B.stops.size();

    int upperA = min(maxLen, nA);
    int upperB = min(maxLen, nB);

    uniform_int_distribution<int> pickLenA(minLen, upperA);
    uniform_int_distribution<int> pickLenB(minLen, upperB);

    int la = pickLenA(rng);
    int lb = pickLenB(rng);

    uniform_int_distribution<int> pickLeftA(0, nA - la);
    uniform_int_distribution<int> pickLeftB(0, nB - lb);

    int leftA = pickLeftA(rng);
    int leftB = pickLeftB(rng);

    int rightA = leftA + la - 1;
    int rightB = leftB + lb - 1;

    auto segA = getSegmentInfo(data, sol, a, leftA, la);
    auto segB = getSegmentInfo(data, sol, b, leftB, lb);

    bool revBtoA = (uniform_int_distribution<int>(0, 1)(rng) == 1);
    bool revAtoB = (uniform_int_distribution<int>(0, 1)(rng) == 1);

    int newLoadA = sol.routeLoad[a] - segA.loadSum + segB.loadSum;
    int newLoadB = sol.routeLoad[b] - segB.loadSum + segA.loadSum;
    if (!enforceCapacity(data, newLoadA) || !enforceCapacity(data, newLoadB)) return false;

    db deltaTravelA = deltaReplaceSegmentTravel(data, sol, a, leftA, rightA, segB, revBtoA);
    db deltaTravelB = deltaReplaceSegmentTravel(data, sol, b, leftB, rightB, segA, revAtoB);

    db newTimeA = (sol.routeTravel[a] + deltaTravelA) + (sol.routeDwell[a] - segA.dwellSum + segB.dwellSum);
    db newTimeB = (sol.routeTravel[b] + deltaTravelB) + (sol.routeDwell[b] - segB.dwellSum + segA.dwellSum);

    db oldCostA = data.routeCost(sol.routeTime[a], sol.routeLoad[a]);
    db oldCostB = data.routeCost(sol.routeTime[b], sol.routeLoad[b]);
    db newCostA = data.routeCost(newTimeA, newLoadA);
    db newCostB = data.routeCost(newTimeB, newLoadB);

    vector<db> delta = { (newCostA - oldCostA) + (newCostB - oldCostB) };

    out.type = MoveType::CrossExchange;
    out.delta = delta;
    out.payload = CrossExchangeMove{a, leftA, la, b, leftB, lb, revBtoA, revAtoB};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<CrossExchangeMove>(cand.payload);

    if (!validRouteIndex(sol, mv.rA) || !validRouteIndex(sol, mv.rB)) return;
    if (mv.rA == mv.rB) return;
    auto& A = sol.routes[mv.rA];
    auto& B = sol.routes[mv.rB];
    if (!validRange(A, mv.leftA, mv.lenA)) return;
    if (!validRange(B, mv.leftB, mv.lenB)) return;

    int rightA = mv.leftA + mv.lenA - 1;
    int rightB = mv.leftB + mv.lenB - 1;

    vector<int> segStopsA(A.stops.begin() + mv.leftA, A.stops.begin() + rightA + 1);
    vector<int> segWeightA(A.weight.begin() + mv.leftA, A.weight.begin() + rightA + 1);

    vector<int> segStopsB(B.stops.begin() + mv.leftB, B.stops.begin() + rightB + 1);
    vector<int> segWeightB(B.weight.begin() + mv.leftB, B.weight.begin() + rightB + 1);

    A.stops.erase(A.stops.begin() + mv.leftA, A.stops.begin() + rightA + 1);
    A.weight.erase(A.weight.begin() + mv.leftA, A.weight.begin() + rightA + 1);

    B.stops.erase(B.stops.begin() + mv.leftB, B.stops.begin() + rightB + 1);
    B.weight.erase(B.weight.begin() + mv.leftB, B.weight.begin() + rightB + 1);

    if (mv.reverseIntoA) {
      reverse(segStopsB.begin(), segStopsB.end());
      reverse(segWeightB.begin(), segWeightB.end());
    }
    if (mv.reverseIntoB) {
      reverse(segStopsA.begin(), segStopsA.end());
      reverse(segWeightA.begin(), segWeightA.end());
    }

    A.stops.insert(A.stops.begin() + mv.leftA, segStopsB.begin(), segStopsB.end());
    A.weight.insert(A.weight.begin() + mv.leftA, segWeightB.begin(), segWeightB.end());

    B.stops.insert(B.stops.begin() + mv.leftB, segStopsA.begin(), segStopsA.end());
    B.weight.insert(B.weight.begin() + mv.leftB, segWeightA.begin(), segWeightA.end());


    cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
  }
};

// =======================
// LNS (k-exchange style): Ruin & Recreate
// - Randomly remove k "visits" (stop, weight) from solution
// - Greedy reinsert each removed visit into best position among all routes,
//   and also allow creating a new route for it.
// This is not the only definition of k-exchange, but is a typical LNS neighborhood.
// =======================
struct KExchangeRuinRecreateOperator : MoveOperator {
  db w = 0.15; // keep low: this is a large neighborhood
  int kMin = 6, kMax = 12;

  string name() const override { return "KExchange(RuinRecreate)"; }
  db weight() const override { return w; }

  static db routeCostOf(const ProblemData& data, const Route& rt) {
    int n = (int)rt.stops.size();
    int load = 0;
    db dwellSum = 0;
    for (int i = 0; i < n; i++) {
      load += rt.weight[i];
      dwellSum += data.dwell(rt.weight[i]);
    }
    db travel = 0;
    if (n) {
      travel += data.driveTime[rt.stops.back()][0];
      for (int i = 1; i < n; i++) travel += data.driveTime[rt.stops[i - 1]][rt.stops[i]];
    }
    return data.routeCost(travel + dwellSum, load);
  }

  // Evaluate insertion of (stop,wt) into route at position pos. Returns delta cost of that route.
  static int routeLoadOf(const Route& rt) {
    int load = 0;
    for (int w : rt.weight) load += w;
    return load;
  }

  // Evaluate insertion of (stop,wt) into route at position pos. Returns delta cost of that route.
  // If hard capacity would be violated, returns a very large number.
  static db bestInsertDeltaForOne(const ProblemData& data, const Route& rt, int stop, int wt, int& bestPos) {
    int load = routeLoadOf(rt);
    if (data.P.hardCapacity && load + wt > data.P.capacity) return 1e100;

    db oldCost = routeCostOf(data, rt);

    int n = (int)rt.stops.size();
    bestPos = 0;
    db bestDelta = 1e100;

    for (int pos = 0; pos <= n; pos++) {
      Route tmp = rt;
      tmp.stops.insert(tmp.stops.begin() + pos, stop);
      tmp.weight.insert(tmp.weight.begin() + pos, wt);
      db newCost = routeCostOf(data, tmp);
      db delta = newCost - oldCost;
      if (delta + EPS < bestDelta) {
        bestDelta = delta;
        bestPos = pos;
      }
    }
    return bestDelta;
  }

  bool sample(const ProblemData& data, const Solution& sol, mt19937& rng, Candidate& out) const override {
    if (sol.routes.empty()) return false;

    // Build a flat list of all visits.
    vector<pair<int,int>> visits;
    visits.reserve(256);
    for (int r = 0; r < (int)sol.routes.size(); r++) {
      for (int i = 0; i < (int)sol.routes[r].stops.size(); i++) visits.push_back({r, i});
    }
    if ((int)visits.size() < 2) return false;

    int k = uniform_int_distribution<int>(kMin, min(kMax, (int)visits.size()))(rng);
    shuffle(visits.begin(), visits.end(), rng);
    visits.resize(k);

    // Group by route.
    sort(visits.begin(), visits.end(), [](auto& x, auto& y){
      if (x.first != y.first) return x.first < y.first;
      return x.second > y.second; // descending pos for safe erases
    });

    vector<int> routeIds;
    routeIds.reserve(k);
    for (auto [r, _] : visits) {
      if (routeIds.empty() || routeIds.back() != r) routeIds.push_back(r);
    }

    // Copy only affected routes.
    vector<Route> newRoutes;
    newRoutes.reserve(routeIds.size());
    for (int rid : routeIds) newRoutes.push_back(sol.routes[rid]);

    // Map routeId -> local index.
    unordered_map<int,int> mp;
    mp.reserve(routeIds.size() * 2);
    for (int i = 0; i < (int)routeIds.size(); i++) mp[routeIds[i]] = i;

    struct Item { int stop, wt; };
    vector<Item> removed;
    removed.reserve(k);

    // Remove chosen visits.
    for (auto [r, pos] : visits) {
      int li = mp[r];
      auto& rt = newRoutes[li];
      if (pos < 0 || pos >= (int)rt.stops.size()) continue;
      removed.push_back({rt.stops[pos], rt.weight[pos]});
      rt.stops.erase(rt.stops.begin() + pos);
      rt.weight.erase(rt.weight.begin() + pos);
    }

    // Greedy reinsert into affected routes only + allow creating new routes.
    vector<Route> appended;
    appended.reserve(k);

    for (auto it : removed) {
      int remaining = it.wt;
      while (remaining > 0) {
        int take = remaining;
        if (data.P.hardCapacity) take = min(take, data.P.capacity);
        remaining -= take;

        int bestLocal = -1;
        int bestPos = 0;
        db bestDelta = 1e100;

        for (int i = 0; i < (int)newRoutes.size(); i++) {
          int pos;
          db d = bestInsertDeltaForOne(data, newRoutes[i], it.stop, take, pos);
          if (d + EPS < bestDelta) {
            bestDelta = d;
            bestLocal = i;
            bestPos = pos;
          }
        }

        // Always allow a new route as fallback.
        Route nr;
        nr.stops.push_back(it.stop);
        nr.weight.push_back(take);
        db newRouteCost = routeCostOf(data, nr);

        // If there is no existing route candidate, or new route is better, create a new route.
        if (bestLocal == -1 || newRouteCost + EPS < bestDelta) {
          appended.push_back(std::move(nr));
        } else {
          auto& rt = newRoutes[bestLocal];
          int p = min(max(bestPos, 0), (int)rt.stops.size());
          rt.stops.insert(rt.stops.begin() + p, it.stop);
          rt.weight.insert(rt.weight.begin() + p, take);
        }
      }
    }

    // Cleanup: merge duplicates in all affected/new routes.

    // Compute delta only on affected routes + appended.
    db oldSum = 0;
    for (int rid : routeIds) {
      oldSum += data.routeCost(sol.routeTime[rid], sol.routeLoad[rid]);
    }

    db newSum = 0;
    for (auto& rt : newRoutes) newSum += routeCostOf(data, rt);
    for (auto& rt : appended) newSum += routeCostOf(data, rt);

    vector<db> delta = { newSum - oldSum };

    out.type = MoveType::KExchange;
    out.delta = delta;
    out.payload = KExchangeMove{routeIds, std::move(newRoutes), std::move(appended)};
    return true;
  }

  void apply(const ProblemData& data, Solution& sol, const Candidate& cand) const override {
    auto mv = get<KExchangeMove>(cand.payload);

    // Replace affected routes.
    for (int i = 0; i < (int)mv.routeIds.size(); i++) {
      int rid = mv.routeIds[i];
      if (0 <= rid && rid < (int)sol.routes.size()) {
        sol.routes[rid] = std::move(mv.newRoutes[i]);
      }
    }

    // Append new routes.
    for (auto& rt : mv.appended) {
      sol.routes.push_back(std::move(rt));
    }

    cleanupEmptyRoutes(sol);
    rebuildAll(data, sol);
  }
};

// =======================
// Local Search: sample moves from a weighted distribution, keep best, then apply
// =======================
struct LocalSearchRandomBest {
  int samplesPerIteration = 2500; // "lặp đủ nhiều lần"
  db timeLimitSeconds = 60;

  vector<unique_ptr<MoveOperator>> ops;
  vector<db> opWeights;

  void finalizeWeights() {
    opWeights.clear();
    opWeights.reserve(ops.size());
    for (auto& op : ops) opWeights.push_back(max<db>(0.0, op->weight()));
    bool allZero = true;
    for (db x : opWeights) if (x > 0) { allZero = false; break; }
    if (allZero) for (db &x : opWeights) x = 1.0;
  }

  void optimize(const ProblemData& data, Solution& sol, mt19937& rng) {
    Timer timer;
    if (timeLimitSeconds > 0) timer.set_limit_seconds(timeLimitSeconds);

    finalizeWeights();
    discrete_distribution<int> pickOp(opWeights.begin(), opWeights.end());

    int objectiveCount = (int)sol.score.size();

    while (!timer.time_up()) {
      bool hasBest = false;
      Candidate best;
      best.delta.assign(objectiveCount, 0);

      for (int t = 0; t < samplesPerIteration; t++) {
        int id = pickOp(rng);

        Candidate cand;
        cand.opId = id;
        cand.delta.assign(objectiveCount, 0);

        if (!ops[id]->sample(data, sol, rng, cand)) continue;

        if (!hasBest || lexBetter(cand.delta, best.delta)) {
          best = std::move(cand);
          hasBest = true;
        }
      }

      if (!hasBest || !lexImproves(best.delta)) break;

      ops[best.opId]->apply(data, sol, best);

      // safety: keep solution compact
      cleanupEmptyRoutes(sol);
      rebuildAll(data, sol);
    }
  }
};

// =======================
// Local Search: best candidate from each operator, then choose best overall
// =======================
struct LocalSearchBestOfEach {
  int samplesPerOperator = 500;
  db timeLimitSeconds = 600;

  vector<unique_ptr<MoveOperator>> ops;

  void optimize(const ProblemData& data, Solution& sol, mt19937& rng) {
    Timer timer;
    if (timeLimitSeconds > 0) timer.set_limit_seconds(timeLimitSeconds);

    int objectiveCount = (int)sol.score.size();

    while (!timer.time_up()) {
      bool hasBest = false;
      Candidate bestOverall;
      bestOverall.delta.assign(objectiveCount, 0);

      for (int i = 0; i < (int)ops.size(); i++) {
        if (ops[i]->weight() <= EPS) continue;

        bool hasOpBest = false;
        Candidate bestOp;
        bestOp.delta.assign(objectiveCount, 0);

        for (int t = 0; t < samplesPerOperator; t++) {
          Candidate cand;
          cand.opId = i;
          cand.delta.assign(objectiveCount, 0);

          if (!ops[i]->sample(data, sol, rng, cand)) continue;

          if (!hasOpBest || lexBetter(cand.delta, bestOp.delta)) {
            bestOp = std::move(cand);
            hasOpBest = true;
          }
        }

        if (hasOpBest && (!hasBest || lexBetter(bestOp.delta, bestOverall.delta))) {
          bestOverall = std::move(bestOp);
          hasBest = true;
        }
      }

      if (!hasBest || !lexImproves(bestOverall.delta)) break;

      ops[bestOverall.opId]->apply(data, sol, bestOverall);

      cleanupEmptyRoutes(sol);
      rebuildAll(data, sol);
    }
  }
};

// =======================
// Initial solution (same as yours): nearest stop assignment + pack by capacity.
// If you use soft capacity, this still gives a decent starting point.
// =======================
static Solution buildInitialSolution(const ProblemData& data, mt19937& rng) {
  ll totalPassengers = 0;
  for (int a = 0; a < data.addressCount; a++) totalPassengers += data.passengers[a];

  int busCount = max(1LL, (ll)ceil(totalPassengers / (db)data.P.capacity));

  Solution sol;
  sol.routes.assign(busCount, Route{});
  sol.assign.assign(data.addressCount, 0);

  for (int a = 0; a < data.addressCount; a++) {
    int bestStop = 0;
    db bestDist = INFINITY;

    for (const auto& opt : data.walkOptions[a]) {
      if (opt.dist <= data.P.maxWalkDistance + EPS) {
        if (opt.dist + EPS < bestDist) {
          bestDist = opt.dist;
          bestStop = opt.stop;
        }
      }
    }

    // If nothing under maxWalkDistance, take the closest available (if any).
    if (bestDist >= INFINITY / 2) {
      for (const auto& opt : data.walkOptions[a]) {
        if (opt.dist + EPS < bestDist) {
          bestDist = opt.dist;
          bestStop = opt.stop;
        }
      }
    }

    sol.assign[a] = bestStop;
  }

  vector<int> demand(data.stopCount, 0);
  for (int a = 0; a < data.addressCount; a++) {
    demand[sol.assign[a]] += data.passengers[a];
  }

  vector<int> load(busCount, 0);
  int r = 0;
  for (int s = 0; s < data.stopCount; s++) {
    int remaining = demand[s];
    while (remaining > 0) {
      while (r < busCount && load[r] == data.P.capacity) r++;

      if (r == busCount) {
        sol.routes.push_back(Route{});
        load.push_back(0);
        busCount++;
      }

      int take = min(remaining, data.P.capacity - load[r]);
      load[r] += take;
      remaining -= take;

      auto& route = sol.routes[r];
      int pos = -1;
      for (int i = 0; i < (int)route.stops.size(); i++) {
        if (route.stops[i] == s) { pos = i; break; }
      }

      if (pos == -1) {
        route.stops.push_back(s);
        route.weight.push_back(take);
      } else {
        route.weight[pos] += take;
      }
    }
  }

  rebuildAll(data, sol);
  return sol;
}

// =======================
// Read input (cin/cout) - unchanged format
// =======================
static ProblemData readProblem() {
  ProblemData data;

  db m_e, m_w, m_t, secPerPassenger, secPerStop;
  int capacity;

  cin >> data.stopCount >> data.addressCount >> data.walkCount
      >> m_e >> m_w >> m_t
      >> capacity >> secPerPassenger >> secPerStop;

  data.P.capacity = capacity;
  data.P.maxWalkDistance = m_w;
  data.P.maxJourneyTime = m_t;
  data.P.secPerPassenger = secPerPassenger;
  data.P.secPerStop = secPerStop;
  data.P.hardCapacity = true;

  // consume stop coordinates (not needed)
  for (int i = 0; i < data.stopCount; i++) {
    db x, y;
    cin >> x >> y;
  }

  // addresses
  data.passengers.assign(data.addressCount, 0);
  for (int i = 0; i < data.addressCount; i++) {
    db x, y;
    int p;
    cin >> x >> y >> p;
    data.passengers[i] = p;
  }

  // consume drive_distance (not needed)
  for (int i = 0; i < data.stopCount; i++) {
    for (int j = 0; j < data.stopCount; j++) {
      db tmp;
      cin >> tmp;
    }
  }

  data.driveTime.assign(data.stopCount, vector<db>(data.stopCount));
  for (int i = 0; i < data.stopCount; i++) {
    for (int j = 0; j < data.stopCount; j++) {
      cin >> data.driveTime[i][j];
    }
  }
  data.walkOptions.assign(data.addressCount, {});

  for (int a = 0; a < data.addressCount; a++) {
    int sz;
    cin >> sz;
    data.walkOptions[a].reserve(sz);
    for (int k = 0; k < sz; k++) {
      int stop;
      db dist, time;
      cin >> stop >> dist >> time;
      // Some datasets index stops 1-based. Make this robust.
      if (stop >= data.stopCount && stop > 0) stop--;
      if (0 <= stop && stop < data.stopCount) {
        data.walkOptions[a].push_back(ProblemData::WalkOption{stop, dist, time});
      }
    }
  }

  return data;
}


// =======================
// Safety repair: ensure the solution serves exactly the demand implied by assign[].
// This prevents "cnt = 0" / dropped passengers due to any buggy move.
// =======================
static vector<ll> computeDemandByStop(const ProblemData& data, const Solution& sol) {
  vector<ll> need(data.stopCount, 0);
  int nA = min((int)sol.assign.size(), data.addressCount);
  for (int a = 0; a < nA; a++) {
    int s = sol.assign[a];
    if (s < 0 || s >= data.stopCount) s = 0;
    need[s] += data.passengers[a];
  }
  return need;
}

static vector<ll> computeHaveByStop(const ProblemData& data, const Solution& sol) {
  vector<ll> have(data.stopCount, 0);
  for (auto& rt : sol.routes) {
    for (int i = 0; i < (int)rt.stops.size(); i++) {
      int s = rt.stops[i];
      int w = rt.weight[i];
      if (w <= 0) continue;
      if (0 <= s && s < data.stopCount) have[s] += w;
    }
  }
  return have;
}

static void repairSolutionToMeetDemand(const ProblemData& data, Solution& sol) {
  if (data.stopCount <= 0) return;

  vector<ll> need = computeDemandByStop(data, sol);
  vector<ll> have = computeHaveByStop(data, sol);

  // 1) Remove any surplus weight (shouldn't happen, but keep it safe).
  for (int s = 0; s < data.stopCount; s++) {
    ll extra = have[s] - need[s];
    if (extra <= 0) continue;

    for (auto& rt : sol.routes) {
      for (int i = 0; i < (int)rt.stops.size() && extra > 0; i++) {
        if (rt.stops[i] != s) continue;
        int take = (int)min<ll>(extra, rt.weight[i]);
        rt.weight[i] -= take;
        extra -= take;
        if (rt.weight[i] == 0) {
          rt.stops.erase(rt.stops.begin() + i);
          rt.weight.erase(rt.weight.begin() + i);
          i--;
        }
      }
      if (extra == 0) break;
    }
  }

  cleanupEmptyRoutes(sol);

  // 2) Fill missing demand by creating new routes (unlimited fleet).
  have = computeHaveByStop(data, sol);

  for (int s = 0; s < data.stopCount; s++) {
    ll missing = need[s] - have[s];
    while (missing > 0) {
      int take = (int)missing;
      if (data.P.hardCapacity) take = min(take, data.P.capacity);
      Route rt;
      rt.stops.push_back(s);
      rt.weight.push_back(take);
      sol.routes.push_back(std::move(rt));
      missing -= take;
    }
  }

  // 3) Enforce hard capacity by splitting overweight routes (if any).
  if (data.P.hardCapacity) {
    for (int r = 0; r < (int)sol.routes.size(); r++) {
      auto& rt = sol.routes[r];

      ll load = 0;
      for (int w : rt.weight) load += w;

      while (load > data.P.capacity && !rt.stops.empty()) {
        int i = (int)rt.stops.size() - 1;
        int s = rt.stops[i];
        int w = rt.weight[i];

        ll overflow = load - data.P.capacity;
        int move = (int)min<ll>(overflow, w);

        Route nr;
        nr.stops.push_back(s);
        nr.weight.push_back(move);
        sol.routes.push_back(std::move(nr));

        rt.weight[i] -= move;
        load -= move;

        if (rt.weight[i] == 0) {
          rt.stops.pop_back();
          rt.weight.pop_back();
        }
      }
    }
  }

  cleanupEmptyRoutes(sol);

  // If there is demand but no routes, create at least one trivial route.
  ll totalNeed = 0;
  for (auto x : need) totalNeed += x;
  if (totalNeed > 0 && sol.routes.empty()) {
    for (int s = 0; s < data.stopCount; s++) if (need[s] > 0) {
      int take = (int)min<ll>(need[s], data.P.capacity);
      Route rt;
      rt.stops.push_back(s);
      rt.weight.push_back(take);
      sol.routes.push_back(std::move(rt));
      break;
    }
  }

  rebuildAll(data, sol);
}

// =======================
// Output: skip empty routes (important if you allow NEW routes)
// =======================
ostream& operator << (ostream& os, const Solution& sol) {
  int cnt = 0;
  for (auto& r : sol.routes) if (!r.stops.empty()) cnt++;

  os << cnt << "\n";
  for (auto& route : sol.routes) {
    if (route.stops.empty()) continue;
    os << route.stops.size();
    for (int i = 0; i < (int)route.stops.size(); i++) {
      os << " " << route.stops[i] << " " << route.weight[i];
    }
    os << "\n";
  }
  for (int a = 0; a < (int)sol.assign.size(); a++) {
    os << sol.assign[a] << " ";
  }
  return os;
}

int main(int argc, char** argv) {
  // if (fopen("input.txt", "r")) {
  //   freopen("input.txt", "r", stdin);
  //   freopen("output.txt", "w", stdout);
  // }

  if (argc >= 2) {
    if (fopen(argv[1], "r")) {
      freopen(argv[1], "r", stdin);
    }
  }
  if (argc >= 3) {
    freopen(argv[2], "w", stdout);
  }

  cin.tie(0)->sync_with_stdio(0);

  ProblemData data = readProblem();
  mt19937 rng((unsigned)chrono::steady_clock::now().time_since_epoch().count());

  Solution sol = buildInitialSolution(data, rng);
  improveAllRoutes2Opt(data, sol, 1);

  LocalSearchBestOfEach ls;
  ls.samplesPerOperator = 500;
  ls.timeLimitSeconds = 600;

  ls.ops.push_back(make_unique<Relocate1Operator>());
  ls.ops.push_back(make_unique<Swap2Operator>());
  ls.ops.push_back(make_unique<TwoOptIntraOperator>());
  ls.ops.push_back(make_unique<TwoOptInterOperator>());
  ls.ops.push_back(make_unique<OrOptOperator>());
  ls.ops.push_back(make_unique<ReassignAddressOperator>());
  ls.ops.push_back(make_unique<StopMergeOperator>());
  ls.ops.push_back(make_unique<SplitRouteOperator>());
  ls.ops.push_back(make_unique<ThreeOptOperator>());
  ls.ops.push_back(make_unique<ThreePointOperator>());
  ls.ops.push_back(make_unique<CrossExchangeOperator>());
  // ls.ops.push_back(make_unique<KExchangeRuinRecreateOperator>());

  ls.optimize(data, sol, rng);

  // Safety: ensure we still serve all passengers after large moves (especially k-exchange).
  repairSolutionToMeetDemand(data, sol);
  improveAllRoutes2Opt(data, sol, 1);


  cout << sol;
  return 0;
}
