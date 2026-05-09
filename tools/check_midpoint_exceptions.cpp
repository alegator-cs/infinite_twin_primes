#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <vector>

using u64 = std::uint64_t;
using u128 = __uint128_t;

namespace {

u64 parse_u64(const std::string& text, const char* flag) {
  std::size_t pos = 0;
  unsigned long long value = 0;
  try {
    value = std::stoull(text, &pos, 10);
  } catch (const std::exception&) {
    std::cerr << "invalid integer for " << flag << ": " << text << "\n";
    std::exit(2);
  }
  if (pos != text.size()) {
    std::cerr << "invalid integer for " << flag << ": " << text << "\n";
    std::exit(2);
  }
  return static_cast<u64>(value);
}

u64 mul_mod(u64 a, u64 b, u64 mod) {
  return static_cast<u64>((static_cast<u128>(a) * static_cast<u128>(b)) % mod);
}

u64 pow_mod(u64 a, u64 e, u64 mod) {
  u64 result = 1 % mod;
  while (e != 0) {
    if ((e & 1) != 0) result = mul_mod(result, a, mod);
    a = mul_mod(a, a, mod);
    e >>= 1;
  }
  return result;
}

bool is_prime64(u64 n) {
  if (n < 2) return false;
  static constexpr u64 small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (u64 p : small) {
    if (n % p == 0) return n == p;
  }

  u64 d = n - 1;
  unsigned s = 0;
  while ((d & 1) == 0) {
    d >>= 1;
    ++s;
  }

  // Deterministic Miller-Rabin bases for all 64-bit unsigned integers.
  static constexpr u64 bases[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
  for (u64 a : bases) {
    if (a % n == 0) continue;
    u64 x = pow_mod(a % n, d, n);
    if (x == 1 || x == n - 1) continue;
    bool witness = true;
    for (unsigned r = 1; r < s; ++r) {
      x = mul_mod(x, x, n);
      if (x == n - 1) {
        witness = false;
        break;
      }
    }
    if (witness) return false;
  }
  return true;
}

std::vector<std::uint32_t> simple_sieve(std::uint32_t n) {
  std::vector<char> is_prime(n + 1, true);
  is_prime[0] = false;
  if (n >= 1) is_prime[1] = false;
  for (std::uint32_t p = 2; static_cast<u64>(p) * p <= n; ++p) {
    if (!is_prime[p]) continue;
    for (u64 j = static_cast<u64>(p) * p; j <= n; j += p) {
      is_prime[static_cast<std::size_t>(j)] = false;
    }
  }
  std::vector<std::uint32_t> primes;
  for (std::uint32_t p = 2; p <= n; ++p) {
    if (is_prime[p]) primes.push_back(p);
  }
  return primes;
}

template <class Fn>
void for_primes_up_to(u64 limit, Fn&& fn) {
  if (limit < 2) return;
  std::uint32_t root = 1;
  while (static_cast<u64>(root + 1) * static_cast<u64>(root + 1) <= limit) ++root;
  const auto base_primes = simple_sieve(root);

  constexpr u64 segment_size = 1ULL << 22;
  for (u64 low = 2; low <= limit;) {
    const u64 high = std::min(limit, low + segment_size - 1);
    std::vector<char> is_prime(static_cast<std::size_t>(high - low + 1), true);

    for (std::uint32_t p32 : base_primes) {
      const u64 p = p32;
      const u64 pp = p * p;
      if (pp > high) break;
      u64 start = ((low + p - 1) / p) * p;
      if (start < pp) start = pp;
      for (u64 j = start; j <= high; j += p) {
        is_prime[static_cast<std::size_t>(j - low)] = false;
      }
    }

    for (u64 n = low; n <= high; ++n) {
      if (is_prime[static_cast<std::size_t>(n - low)]) fn(n);
    }

    if (high == std::numeric_limits<u64>::max()) break;
    low = high + 1;
  }
}

struct Survivor {
  bool found = false;
  u64 h = 0;
};

Survivor first_midpoint_twin_index(u64 r) {
  if (r == 2) return {};
  if (r == 3) {
    for (u64 h = 1; h < r; ++h) {
      if (is_prime64(r * h - 1) && is_prime64(r * h + 1)) return {true, h};
    }
    return {};
  }

  // For odd r > 3, a twin midpoint rh must be 0 mod 6:
  // h odd makes both neighbors even, and h not divisible by 3 makes one
  // neighbor divisible by 3.
  for (u64 h = 6; h < r; h += 6) {
    const u64 m = r * h;
    if (is_prime64(m - 1) && is_prime64(m + 1)) return {true, h};
  }
  return {};
}

std::vector<u64> parse_csv_u64(const std::string& csv) {
  std::vector<u64> result;
  std::stringstream ss(csv);
  std::string part;
  while (std::getline(ss, part, ',')) {
    if (part.empty()) continue;
    result.push_back(parse_u64(part, "--expected"));
  }
  return result;
}

std::string join_u64(const std::vector<u64>& values) {
  std::ostringstream out;
  for (std::size_t i = 0; i < values.size(); ++i) {
    if (i != 0) out << ", ";
    out << values[i];
  }
  return out.str();
}

void print_help(const char* argv0) {
  std::cout
      << "Usage: " << argv0 << " [--limit N] [--expected csv|none]\n"
      << "       [--progress prime_count] [--show-survivors]\n\n"
      << "Checks midpoint-exceptional primes r <= N. A prime r is exceptional\n"
      << "when no 1 <= h < r makes both rh-1 and rh+1 prime.\n\n"
      << "Default N is 1000000000. The default expected list is the known\n"
      << "exception list through that bound: 2,5,11,13,31,37,53,61,73,79,97,127.\n";
}

}  // namespace

int main(int argc, char** argv) {
  u64 limit = 1000000000ULL;
  u64 progress_every = 0;
  bool show_survivors = false;
  bool verify_expected = true;
  std::vector<u64> expected = {2, 5, 11, 13, 31, 37, 53, 61, 73, 79, 97, 127};

  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    auto need_value = [&](const char* flag) -> std::string {
      if (i + 1 >= argc) {
        std::cerr << "missing value after " << flag << "\n";
        std::exit(2);
      }
      return argv[++i];
    };

    if (arg == "--help" || arg == "-h") {
      print_help(argv[0]);
      return 0;
    } else if (arg == "--limit") {
      limit = parse_u64(need_value("--limit"), "--limit");
    } else if (arg == "--progress") {
      progress_every = parse_u64(need_value("--progress"), "--progress");
    } else if (arg == "--show-survivors") {
      show_survivors = true;
    } else if (arg == "--expected") {
      const std::string value = need_value("--expected");
      if (value == "none") {
        verify_expected = false;
        expected.clear();
      } else {
        expected = parse_csv_u64(value);
        verify_expected = true;
      }
    } else {
      std::cerr << "unknown argument: " << arg << "\n";
      print_help(argv[0]);
      return 2;
    }
  }

  std::vector<u64> exceptions;
  u64 prime_count = 0;
  const auto started = std::chrono::steady_clock::now();

  for_primes_up_to(limit, [&](u64 r) {
    ++prime_count;
    const Survivor survivor = first_midpoint_twin_index(r);
    if (!survivor.found) {
      exceptions.push_back(r);
      std::cout << "exception r=" << r << "\n";
    } else if (show_survivors) {
      std::cout << "survivor r=" << r << " h=" << survivor.h
                << " twins=(" << (r * survivor.h - 1) << ", "
                << (r * survivor.h + 1) << ")\n";
    }
    if (progress_every != 0 && prime_count % progress_every == 0) {
      const auto now = std::chrono::steady_clock::now();
      const double seconds =
          std::chrono::duration_cast<std::chrono::duration<double>>(now - started).count();
      std::cerr << "checked " << prime_count << " primes; current r=" << r
                << "; elapsed=" << seconds << "s\n";
    }
  });

  std::cout << "limit=" << limit << "\n";
  std::cout << "prime_count=" << prime_count << "\n";
  std::cout << "exceptions={" << join_u64(exceptions) << "}\n";

  if (verify_expected) {
    std::vector<u64> expected_here;
    for (u64 r : expected) {
      if (r <= limit) expected_here.push_back(r);
    }
    if (exceptions != expected_here) {
      std::cerr << "expected exceptions={" << join_u64(expected_here) << "}\n";
      std::cerr << "found exceptions={" << join_u64(exceptions) << "}\n";
      return 1;
    }
    std::cout << "expected_list_verified=yes\n";
  }

  if (!exceptions.empty()) {
    std::cout << "last_exception=" << exceptions.back() << "\n";
    if (exceptions.back() == 127 && limit >= 127) {
      std::cout << "no_exception_in=(127," << limit << "]\n";
    }
  }

  return 0;
}
