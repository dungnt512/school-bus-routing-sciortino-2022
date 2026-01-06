#include <bits/stdc++.h>
using namespace std;

using ll = long long;
using db = double;
using ld = long double;

const db eps = 1e-9;

// string DIR = "opt_10s";
string DIR = ".";

template<class U, class V>
ostream& operator << (ostream &os, pair<U, V> p) {
  os << p.first << " " << p.second;
  return os;
}

struct Walk {
  int stop;
  db time = INFINITY, distance = INFINITY;
};

int solve(string filename) {
  // freopen("test.in", "r", stdin);
  string INP_DIR = DIR + "/" + filename + ".in";
  string OUT_DIR = DIR + "/" + filename + ".out";
  string ANS_DIR = DIR + "/" + filename + ".txt3";

  ifstream fin(INP_DIR);

  int num_stop, num_addr, num_walks, capacity;
  db m_e, m_w, sec_per_passenger, ser_per_stop, m_t;
  // scanf("%d %d %d %lf %lf %lf %d %lf %lf", &num_stop, &num_addr, &num_walks, &m_e, &m_w, &m_t, &capacity, &sec_per_passenger, &ser_per_stop);
  fin >> num_stop >> num_addr >> num_walks >> m_e >> m_w >> m_t >> capacity >> sec_per_passenger >> ser_per_stop;
  m_t *= 60;

  vector<db> x(num_stop), y(num_stop);
  for (int i = 0; i < num_stop; i++) {
    // scanf("%lf %lf", &x[i], &y[i]);
    fin >> x[i] >> y[i];
  }
  vector<db> addr_x(num_addr), addr_y(num_addr);
  vector<int> num_passengers(num_addr);
  for (int i = 0; i < num_addr; i++) {
    // scanf("%d", &num_passengers[i]);
    // scanf("%lf %lf %d", &addr_x[i], &addr_y[i], &num_passengers[i]);
    fin >> addr_x[i] >> addr_y[i] >> num_passengers[i];
  }
  vector<vector<db>> drive_distance(num_stop, vector<db>(num_stop));
  for (int i = 0; i < num_stop; i++) {
    for (int j = 0; j < num_stop; j++) {
      // scanf("%lf", &drive_distance[i][j]);
      fin >> drive_distance[i][j];
    }
  }
  vector<vector<db>> drive_time(num_stop, vector<db>(num_stop));
  for (int i = 0; i < num_stop; i++) {
    for (int j = 0; j < num_stop; j++) {
      // scanf("%lf", &drive_time[i][j]);
      fin >> drive_time[i][j];
    }
  }
  vector<vector<db>> walk_time(num_addr, vector<db>(num_stop, INFINITY));
  vector<vector<db>> walk_distance(num_addr, vector<db>(num_stop, INFINITY));
  for (int i = 0; i < num_addr; i++) {
    int size;
    // scanf("%d", &size);
    fin >> size;
    for (int j = 0; j < size; j++) {
      int stop;
      db time, distance;
      // scanf("%d %lf %lf", &stop, &distance, &time);
      fin >> stop >> distance >> time;
      walk_time[i][stop] = time;
      walk_distance[i][stop] = distance;
    }
  }


  auto calc = [&](istream& is) -> pair<int, db> {
    int n_bus;
    // scanf("%d", &n_bus);
    is >> n_bus;
    db obj = 0;
    vector<int> tot(num_stop, 0);
    for (int i = 0; i < n_bus; i++) {
      int route_size;
      // scanf("%d", &route_size);
      is >> route_size;
      vector<int> route(route_size), weight(route_size);
      int tot_c = 0;
      set<int> used;
      for (int j = 0; j < route_size; j++) {
        // scanf("%d %d", &route[j], &weight[j]);
        is >> route[j] >> weight[j];
        if (!route[j]) 
          return {-1, -1};
        if (used.find(route[j]) != end(used))
          return {-1, -1};
        used.insert(route[j]);
        tot[route[j]] += weight[j];
        tot_c += weight[j];
      }
      if (tot_c > capacity) 
        return {-1, -1};
      db T = drive_time[route.back()][0];
      for (int i = 1; i < route_size; i++) {
        T += drive_time[route[i - 1]][route[i]];
      }
      for (int i = 0; i < route_size; i++) {
        T += ser_per_stop;
        T += sec_per_passenger * weight[i];
      }
      if (T > m_t + eps) 
        // obj += m_t + m_t * (1 + T - m_t);
        return {-1, -1};
      else 
        obj += T;
    }
    vector<int> assign(num_addr), tot_a(num_stop, 0);
    for (int j = 0; j < num_addr; j++) {
      // scanf("%d", &assign[j]);
      is >> assign[j];
      if (walk_distance[j][assign[j]] > m_w + eps) 
        return {-1, -1};
      tot_a[assign[j]] += num_passengers[j];
    }

    for (int i = 0; i < num_stop; i++) {
      // if (tot[i] < tot_a[i]) 
      if (tot[i] != tot_a[i])
        return {-1, -1};
    }

    return {n_bus, obj};
  };

  ll startTime = chrono::steady_clock::now().time_since_epoch().count();
  system((".\\solver_ls_run " + INP_DIR + " " + ANS_DIR).c_str());
  ll endTime = chrono::steady_clock::now().time_since_epoch().count();
  cout << filename << " Time: " << (endTime - startTime) / 1e9 << " s\n";
  cerr << filename << " Time: " << (endTime - startTime) / 1e9 << " s\n";

  ifstream fans(OUT_DIR);
  ifstream fout(ANS_DIR);
  auto w_ans = calc(fans);
  auto w_out = calc(fout);
  if (w_ans.first < 0) {
    // printf("%d Invalid solution from jury\n", -2);
    cout << filename << " " << -2 << " Invalid solution from jury\n";
    cerr << filename << " " << -2 << " Invalid solution from jury\n";
    return 0;
  }
  if (w_out.first < 0) {
    // printf("%d Invalid solution from participant\n", -2);
    cout << filename << " " << -2 << " Invalid solution from participant\n";
    cerr << filename << " " << -2 << " Invalid solution from participant\n";
    return 0;
  }
  if (w_out < w_ans) {
    // printf("%d Better solution! Jury = %lf Participant = %lf\n", 1, w_ans, w_out);
    cout << filename << " " << 1 << " Better solution! Jury = " << w_ans << " Participant = " << w_out << "\n";
    cerr << filename << " " << 1 << " Better solution! Jury = " << w_ans << " Participant = " << w_out << "\n";
  }
  else if (w_out > w_ans) {
    // printf("%d Worse solution! Jury = %lf Participant = %lf\n", -1, w_ans, w_out);
    cout << filename << " " << -1 << " Worse solution! Jury = " << w_ans << " Participant = " << w_out << "\n";
    cerr << filename << " " << -1 << " Worse solution! Jury = " << w_ans << " Participant = " << w_out << "\n";
  }
  else {
    // printf("%d Equal solution! Jury = Participant = %lf\n", 0, w_ans, w_out);
    cout << filename << " " << 0 << " Equal solution! Jury = Participant = " << w_ans << "\n";
    cerr << filename << " " << 0 << " Equal solution! Jury = Participant = " << w_ans << "\n";
  }

  return 0;
}

int main(int argc, char** argv) {
  ll curTime = chrono::steady_clock::now().time_since_epoch().count();
  freopen(("log_" + to_string(curTime)).c_str(), "w", stdout);
  if (argc > 1) {
    DIR = argv[1];
  }

  // cin.tie(0)->sync_with_stdio(0); 

  // for (int i = 0; i < 10; i++) {
  for (int i = 0; i < 20; i++) {
    string filename = to_string(i);
    solve(filename);
  }

  return 0;
}