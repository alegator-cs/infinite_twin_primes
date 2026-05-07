#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

using u64 = unsigned long long;
using u128 = unsigned __int128;

static u64 mod_mul(u64 a, u64 b, u64 m) {
  return static_cast<u128>(a) * b % m;
}

static u64 mod_pow(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  while (e) {
    if (e & 1) r = mod_mul(r, a, m);
    a = mod_mul(a, a, m);
    e >>= 1;
  }
  return r;
}

static bool is_prime(u64 n) {
  if (n < 2) return false;
  static const u64 small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (u64 p : small) {
    if (n % p == 0) return n == p;
  }
  u64 d = n - 1, s = 0;
  while ((d & 1) == 0) {
    d >>= 1;
    ++s;
  }
  static const u64 bases[] = {2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL,
                              9780504ULL, 1795265022ULL};
  for (u64 a : bases) {
    if (a % n == 0) continue;
    u64 x = mod_pow(a, d, n);
    if (x == 1 || x == n - 1) continue;
    bool ok = false;
    for (u64 r = 1; r < s; ++r) {
      x = mod_mul(x, x, n);
      if (x == n - 1) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

static std::vector<u64> primes_upto(u64 n) {
  std::vector<bool> composite(n + 1, false);
  std::vector<u64> primes;
  for (u64 p = 2; p <= n; ++p) {
    if (composite[p]) continue;
    primes.push_back(p);
    if (p <= n / p) {
      for (u64 q = p * p; q <= n; q += p) composite[q] = true;
    }
  }
  return primes;
}

struct ResidueKey {
  u64 r_mod;
  u64 d_mod;
  bool operator<(const ResidueKey& o) const {
    return std::tie(r_mod, d_mod) < std::tie(o.r_mod, o.d_mod);
  }
};

static constexpr u64 wheel = 2ULL * 3 * 5 * 7 * 11 * 13;
static const std::array<u64, 6> wheel_primes = {2, 3, 5, 7, 11, 13};

static std::map<ResidueKey, std::vector<u64>> residue_cache;

static const std::vector<u64>& allowed_residues(u64 r, u64 d) {
  ResidueKey key{r % wheel, d % wheel};
  auto it = residue_cache.find(key);
  if (it != residue_cache.end()) return it->second;
  std::vector<u64> residues;
  for (u64 h = 0; h < wheel; ++h) {
    bool ok = true;
    for (u64 p : wheel_primes) {
      const u64 x = (r % p) * (h % p) % p;
      const u64 dm = d % p;
      if ((x + p - dm) % p == 0 || (x + dm) % p == 0) {
        ok = false;
        break;
      }
    }
    if (ok) residues.push_back(h);
  }
  auto [pos, _] = residue_cache.emplace(key, std::move(residues));
  return pos->second;
}

static bool has_pair_witness(u64 r, u64 d, u64& h_out) {
  if (r <= d + 2) return false;
  const auto& residues = allowed_residues(r, d);
  for (u64 res : residues) {
    u64 h = (res == 0 ? wheel : res);
    for (; h < r; h += wheel) {
      const u64 minus = r * h - d;
      const u64 plus = r * h + d;
      if (is_prime(minus) && is_prime(plus)) {
        h_out = h;
        return true;
      }
    }
  }
  return false;
}

static bool is_square_mod_prime(u64 a, u64 p) {
  if (p == 2) return true;
  a %= p;
  if (a == 0) return true;
  return mod_pow(a, (p - 1) / 2, p) == 1;
}

int main(int argc, char** argv) {
  u64 max_d = 12;
  u64 max_r = 191264;
  bool no_families = false;
  std::vector<u64> d_values;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto need = [&]() -> std::string {
      if (++i >= argc) throw std::runtime_error("missing value after " + a);
      return argv[i];
    };
    if (a == "--max-d") max_d = std::stoull(need());
    else if (a == "--max-r") max_r = std::stoull(need());
    else if (a == "--no-families") no_families = true;
    else if (a == "--d-list") {
      std::stringstream ss(need());
      std::string part;
      while (std::getline(ss, part, ',')) {
        if (!part.empty()) d_values.push_back(std::stoull(part));
      }
    }
    else throw std::runtime_error("unknown argument " + a);
  }
  if (d_values.empty()) {
    for (u64 d = 1; d <= max_d; ++d) d_values.push_back(d);
  } else {
    max_d = *std::max_element(d_values.begin(), d_values.end());
  }

  const auto primes = primes_upto(max_r);

  std::cout << "fixed-gap midpoint-row scan, max_d=" << max_d
            << " max_r=" << max_r << " wheel=" << wheel << "\n\n";
  std::cout << "d gap checked_primes exceptions last_exception first_exception_after_127"
               " first_witness_after_127\n";
  for (u64 d : d_values) {
    u64 checked = 0, exceptions = 0, last_exception = 0;
    u64 first_after_127 = 0, first_witness_after_127 = 0;
    for (u64 r : primes) {
      if (r <= d + 2) continue;
      ++checked;
      u64 h = 0;
      const bool ok = has_pair_witness(r, d, h);
      if (!ok) {
        ++exceptions;
        last_exception = r;
        if (r > 127 && first_after_127 == 0) first_after_127 = r;
      } else if (r > 127 && first_witness_after_127 == 0) {
        first_witness_after_127 = r * h;
      }
    }
    std::cout << d << ' ' << (2 * d) << ' ' << checked << ' ' << exceptions
              << ' ' << last_exception << ' ' << first_after_127 << ' '
              << first_witness_after_127 << "\n" << std::flush;
  }

  if (no_families) return 0;

  std::cout << "\nquadratic identity families for gap 2d:\n";
  std::cout << "For A*B=2d, Delta=A^2+B^2 and\n";
  std::cout << "  u(u+A+B)+d +/- d = u(u+A+B), (u+A)(u+B).\n\n";
  for (u64 d : d_values) {
    std::cout << "d=" << d << " gap=" << 2 * d << ":";
    for (u64 A = 1; A * A <= 2 * d; ++A) {
      if ((2 * d) % A != 0) continue;
      const u64 B = (2 * d) / A;
      const u64 delta = A * A + B * B;
      u64 split = 0, eligible = 0;
      for (u64 p : primes) {
        if (p <= 31 || p == delta) continue;
        ++eligible;
        if (is_square_mod_prime(delta, p)) ++split;
      }
      const double rate = eligible ? static_cast<double>(split) / eligible : 0.0;
      std::cout << " [A=" << A << ",B=" << B << ",Delta=" << delta
                << ",splitRate=" << rate << "]";
    }
    std::cout << "\n";
  }
}
