#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace std;
using u64 = uint64_t;
using u128 = unsigned __int128;

struct Row {
  char typ;
  u64 u;
  u64 h;
  array<u64, 5> vals;
};

static string read_file(const string& path) {
  ifstream in(path, ios::binary);
  if (!in) throw runtime_error("cannot open " + path);
  return string((istreambuf_iterator<char>(in)), istreambuf_iterator<char>());
}

static size_t matching_bracket(const string& s, size_t open) {
  int depth = 0;
  for (size_t i = open; i < s.size(); ++i) {
    if (s[i] == '[') ++depth;
    if (s[i] == ']') {
      --depth;
      if (depth == 0) return i;
    }
  }
  throw runtime_error("unmatched bracket");
}

static vector<u64> parse_array(const string& s, const string& key) {
  size_t pos = s.find("\"" + key + "\"");
  if (pos == string::npos) throw runtime_error("missing key " + key);
  size_t open = s.find('[', pos);
  size_t close = matching_bracket(s, open);
  vector<u64> out;
  u64 cur = 0;
  bool in_num = false;
  for (size_t i = open + 1; i < close; ++i) {
    char c = s[i];
    if ('0' <= c && c <= '9') {
      in_num = true;
      cur = cur * 10 + (u64)(c - '0');
    } else if (in_num) {
      out.push_back(cur);
      cur = 0;
      in_num = false;
    }
  }
  if (in_num) out.push_back(cur);
  return out;
}

static u64 parse_scalar(const string& s, const string& key) {
  size_t pos = s.find("\"" + key + "\"");
  if (pos == string::npos) throw runtime_error("missing key " + key);
  pos = s.find(':', pos);
  ++pos;
  while (pos < s.size() && !isdigit((unsigned char)s[pos])) ++pos;
  u64 v = 0;
  while (pos < s.size() && isdigit((unsigned char)s[pos])) {
    v = v * 10 + (u64)(s[pos] - '0');
    ++pos;
  }
  return v;
}

static bool is_prime(u64 n) {
  if (n < 2) return false;
  if (n % 2 == 0) return n == 2;
  for (u64 d = 3; d * d <= n; d += 2) {
    if (n % d == 0) return false;
  }
  return true;
}

static u64 mod_pow(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  u64 b = a % m;
  while (e) {
    if (e & 1) r = (u64)((u128)r * b % m);
    b = (u64)((u128)b * b % m);
    e >>= 1;
  }
  return r;
}

static bool leg5(u64 p) {
  if (p == 5) return true;
  return mod_pow(5, (p - 1) / 2, p) == 1;
}

static vector<u64> sqrt5_mod_prime(u64 p) {
  vector<u64> out;
  for (u64 x = 0; x < p; ++x) {
    if ((u64)((u128)x * x % p) == 5 % p) out.push_back(x);
  }
  return out;
}

static unordered_map<u64, vector<Row>> row_cache;

static vector<Row> rows_for(u64 p) {
  auto it = row_cache.find(p);
  if (it != row_cache.end()) return it->second;
  vector<Row> out;
  if (!is_prime(p) || !leg5(p)) {
    row_cache[p] = out;
    return out;
  }
  u64 inv2 = (p + 1) / 2;
  for (u64 s : sqrt5_mod_prime(p)) {
    for (auto [typ, c] : vector<pair<char, u64>>{{'R', 5}, {'L', 3}}) {
      u64 u = ((p + s + p - (c % p)) % p);
      u = (u64)((u128)u * inv2 % p);
      u128 mid = (typ == 'R')
        ? ((u128)(u + 1) * (u + 4) + 1)
        : ((u128)u * (u + 3) + 1);
      if (mid % p != 0) continue;
      u64 h = (u64)(mid / p);
      if (1 <= h && h < p) out.push_back(Row{typ, u, h, {u, u+1, u+2, u+3, u+4}});
    }
  }
  row_cache[p] = out;
  return out;
}

static vector<u64> factors(u64 n) {
  vector<u64> out;
  for (u64 d = 2; d * d <= n; d += (d == 2 ? 1 : 2)) {
    while (n % d == 0) {
      out.push_back(d);
      n /= d;
    }
  }
  if (n > 1) out.push_back(n);
  return out;
}

struct Cert {
  u64 X;
  unordered_set<u64> base, mp, pm;
};

static Cert load_cert(const string& path) {
  string s = read_file(path);
  Cert c;
  c.X = parse_scalar(s, "X");
  for (u64 u : parse_array(s, "base")) c.base.insert(u);
  for (u64 u : parse_array(s, "mp")) c.mp.insert(u);
  for (u64 u : parse_array(s, "pm")) c.pm.insert(u);
  return c;
}

struct Step {
  u64 p;
  Row row;
  u64 child;
  u64 childSlot;
};

struct Target {
  u64 p;
  Row row;
  u64 u;
  bool mp;
  bool pm;
};

static bool target_at(const Cert& cert, u64 p, Target& target) {
  for (const Row& row : rows_for(p)) {
    for (u64 u = row.u; u < cert.X; u += p) {
      if (cert.base.count(u)) {
        target = Target{p, row, u, cert.mp.count(u) != 0, cert.pm.count(u) != 0};
        return true;
      }
    }
  }
  return false;
}

static bool dfs(const Cert& cert, u64 p, vector<Step>& path, Target& target,
                unordered_set<u64>& seen, int depth, bool require_child,
                size_t min_steps) {
  if ((!require_child || !path.empty()) && path.size() >= min_steps &&
      target_at(cert, p, target)) return true;
  if (depth > 12 || seen.count(p)) return false;
  seen.insert(p);
  vector<tuple<u64, Row, u64>> children;
  for (const Row& row : rows_for(p)) {
    for (u64 v : row.vals) {
      vector<u64> fs = factors(v);
      set<u64> distinct(fs.begin(), fs.end());
      for (u64 q : distinct) {
        if (31 <= q && q < p && is_prime(q) && leg5(q)) {
          children.push_back({q, row, v});
        }
      }
    }
  }
  sort(children.begin(), children.end(),
    [](const auto& a, const auto& b) { return get<0>(a) > get<0>(b); });
  for (auto [q, row, slot] : children) {
    path.push_back(Step{p, row, q, slot});
    if (dfs(cert, q, path, target, seen, depth + 1, require_child, min_steps)) return true;
    path.pop_back();
  }
  return false;
}

int main(int argc, char** argv) {
  string cert_path = "certificates/generated_mppm_pressure_certificate.json";
  u64 start = 191281;
  bool require_child = false;
  bool list_children = false;
  size_t min_steps = 0;
  u64 scan_split = 0;
  for (int i = 1; i < argc; ++i) {
    string a = argv[i];
    if (a == "--cert" && i + 1 < argc) cert_path = argv[++i];
    else if (a == "--start" && i + 1 < argc) start = stoull(argv[++i]);
    else if (a == "--require-child") require_child = true;
    else if (a == "--list-children") list_children = true;
    else if (a == "--min-steps" && i + 1 < argc) min_steps = stoull(argv[++i]);
    else if (a == "--scan-split" && i + 1 < argc) scan_split = stoull(argv[++i]);
  }
  Cert cert = load_cert(cert_path);
  if (list_children) {
    for (const Row& row : rows_for(start)) {
      cout << "row p=" << start << " typ=" << row.typ << " u=" << row.u
           << " h=" << row.h << "\n";
      for (u64 v : row.vals) {
        vector<u64> fs = factors(v);
        set<u64> distinct(fs.begin(), fs.end());
        for (u64 q : distinct) {
          if (31 <= q && q < start && is_prime(q) && leg5(q)) {
            Target t{};
            cout << "  slot=" << v << " child=" << q
                 << " childTargets=" << (target_at(cert, q, t) ? 1 : 0);
            if (target_at(cert, q, t)) {
              cout << " target_u=" << t.u << " target_p=" << t.p
                   << " target_row=" << t.row.typ;
            }
            cout << "\n";
          }
        }
      }
    }
    return 0;
  }

  if (scan_split > 0) {
    u64 seen_split = 0;
    for (u64 p = start; seen_split < scan_split; ++p) {
      if (!is_prime(p) || !leg5(p)) continue;
      ++seen_split;
      vector<Step> path;
      Target target{};
      unordered_set<u64> seen;
      if (dfs(cert, p, path, target, seen, 0, require_child, min_steps)) {
        cout << "start=" << p << "\n";
        for (const Step& s : path) {
          cout << "step p=" << s.p
               << " row=" << s.row.typ
               << " u=" << s.row.u
               << " h=" << s.row.h
               << " slot=" << s.childSlot
               << " child=" << s.child << "\n";
        }
        cout << "target p=" << target.p
             << " row=" << target.row.typ
             << " row_u=" << target.row.u
             << " h=" << target.row.h
             << " event_u=" << target.u
             << " mp=" << (target.mp ? 1 : 0)
             << " pm=" << (target.pm ? 1 : 0) << "\n";
        return 0;
      }
    }
    cerr << "no path found in scan\n";
    return 1;
  }

  vector<Step> path;
  Target target{};
  unordered_set<u64> seen;
  if (!dfs(cert, start, path, target, seen, 0, require_child, min_steps)) {
    cerr << "no path found\n";
    return 1;
  }
  cout << "start=" << start << "\n";
  for (const Step& s : path) {
    cout << "step p=" << s.p
         << " row=" << s.row.typ
         << " u=" << s.row.u
         << " h=" << s.row.h
         << " slot=" << s.childSlot
         << " child=" << s.child << "\n";
  }
  cout << "target p=" << target.p
       << " row=" << target.row.typ
       << " row_u=" << target.row.u
       << " h=" << target.row.h
       << " event_u=" << target.u
       << " mp=" << (target.mp ? 1 : 0)
       << " pm=" << (target.pm ? 1 : 0) << "\n";
  return 0;
}
