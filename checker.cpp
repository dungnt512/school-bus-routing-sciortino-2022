#include <bits/stdc++.h>
using namespace std;

using ll = long long;
using db = double;
using ld = long double;

const db eps = 1e-9;

struct Walk {
  int stop;
  db time = INFINITY, distance = INFINITY;
};

int main() {
  freopen("test.in", "r", stdin);

  int num_stop, num_addr, num_walks, capacity;
  db m_e, m_w, sec_per_passenger, ser_per_stop, m_t;
  scanf("%d %d %d %lf %lf %lf %d %lf %lf", &num_stop, &num_addr, &num_walks, &m_e, &m_w, &m_t, &capacity, &sec_per_passenger, &ser_per_stop);

  vector<db> x(num_stop), y(num_stop);
  for (int i = 0; i < num_stop; i++) {
    scanf("%lf %lf", &x[i], &y[i]);
  }
  vector<db> addr_x(num_addr), addr_y(num_addr);
  vector<int> num_passengers(num_addr);
  for (int i = 0; i < num_addr; i++) {
    // scanf("%d", &num_passengers[i]);
    scanf("%lf %lf %d", &addr_x[i], &addr_y[i], &num_passengers[i]);
  }
  vector<vector<db>> drive_distance(num_stop, vector<db>(num_stop));
  for (int i = 0; i < num_stop; i++) {
    for (int j = 0; j < num_stop; j++) {
      scanf("%lf", &drive_distance[i][j]);
    }
  }
  vector<vector<db>> drive_time(num_stop, vector<db>(num_stop));
  for (int i = 0; i < num_stop; i++) {
    for (int j = 0; j < num_stop; j++) {
      scanf("%lf", &drive_time[i][j]);
    }
  }
  vector<vector<db>> walk_time(num_addr, vector<db>(num_stop, INFINITY));
  vector<vector<db>> walk_distance(num_addr, vector<db>(num_stop, INFINITY));
  for (int i = 0; i < num_addr; i++) {
    int size;
    scanf("%d", &size);
    for (int j = 0; j < size; j++) {
      int stop;
      db time, distance;
      scanf("%d %lf %lf", &stop, &distance, &time);
      walk_time[i][stop] = time;
      walk_distance[i][stop] = distance;
    }
  }


  auto calc = [&]() -> db {
    int n_bus;
    scanf("%d", &n_bus);
    db obj = 0;
    vector<int> tot(num_stop, 0);
    for (int i = 0; i < n_bus; i++) {
      int route_size;
      scanf("%d", &route_size);
      vector<int> route(route_size), weight(route_size);
      int tot_c = 0;
      for (int j = 0; j < route_size; j++) {
        scanf("%d %d", &route[j], &weight[j]);
        tot[route[j]] += weight[j];
        tot_c += weight[j];
      }
      if (tot_c > capacity) 
        return -1;
      db T = drive_time[route.back()][0];
      for (int i = 1; i < route_size; i++) {
        T += drive_time[route[i - 1]][route[i]];
      }
      for (int i = 0; i < route_size; i++) {
        T += ser_per_stop;
        T += sec_per_passenger * weight[i];
      }
      if (T > m_t + eps) 
        obj += m_t + m_t * (1 + T - m_t);
      else 
        obj += T;
    }
    vector<int> assign(num_addr), tot_a(num_stop, 0);
    for (int j = 0; j < num_addr; j++) {
      scanf("%d", &assign[j]);
      if (walk_distance[j][assign[j]] > m_w + eps) 
        return -1;
      tot_a[assign[j]] += num_passengers[j];
    }

    for (int i = 0; i < num_stop; i++) {
      if (tot[i] < tot_a[i]) 
        return -1;
    }

    return obj;
  };

  db w_ans = calc();
  db w_out = calc();
  if (w_ans < 0) {
    printf("%d Invalid solution from jury\n", -2);
    return 0;
  }
  if (w_out < 0) {
    printf("%d Invalid solution from participant\n", -2);
    return 0;
  }
  if (w_out + eps < w_ans) 
    printf("%d Better solution! Jury = %lf Participant = %lf\n", 1, w_ans, w_out);
  else if (w_out > w_ans + eps) 
    printf("%d Worse solution! Jury = %lf Participant = %lf\n", -1, w_ans, w_out);
  else 
    printf("%d Equal solution! Jury = Participant = %lf\n", 0, w_ans, w_out);

  return 0;
}