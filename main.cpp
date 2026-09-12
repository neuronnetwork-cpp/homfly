#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <tuple>
#include <vector>
#include <algorithm>
#include <cstdlib>

using namespace std;

static int mygcd(int a, int b) {
    a = abs(a);
    b = abs(b);
    while (b) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a;
}

typedef tuple<int, int, int> Exp;

static string superscript(int e) {
    static const string d[10] = {
        "\u2070", "\u00b9", "\u00b2", "\u00b3", "\u2074",
        "\u2075", "\u2076", "\u2077", "\u2078", "\u2079"
    };
    bool neg = e < 0;
    int a = neg ? -e : e;
    string digits;
    if (a == 0)
        digits = d[0];
    while (a > 0) {
        digits = d[a % 10] + digits;
        a /= 10;
    }
    return (neg ? "\u207b" : "") + digits;
}

class Polynomial {
public:
    map<Exp, int> terms;
    bool jones;

    Polynomial(bool j = false)
        : jones(j) {}

    Polynomial(int c, bool j = false)
        : jones(j) {
        if (c != 0)
            terms[Exp(0, 0, 0)] = c;
    }

    static Polynomial monomial(int slot, int e, int coeff, bool j) {
        Polynomial p(j);
        int a = (slot == 0) ? e : 0;
        int b = (slot == 1) ? e : 0;
        int c = (slot == 2) ? e : 0;
        p.terms[Exp(a, b, c)] = coeff;
        return p;
    }

    Polynomial operator+(const Polynomial& o) const {
        Polynomial r(jones);
        r.terms = terms;
        for (const auto& kv : o.terms) {
            r.terms[kv.first] += kv.second;
            if (r.terms[kv.first] == 0)
                r.terms.erase(kv.first);
        }
        return r;
    }

    Polynomial operator-() const {
        Polynomial r(jones);
        for (const auto& kv : terms)
            r.terms[kv.first] = -kv.second;
        return r;
    }

    Polynomial operator-(const Polynomial& o) const {
        return *this + (-o);
    }

    Polynomial operator*(const Polynomial& o) const {
        Polynomial r(jones);
        for (const auto& a : terms) {
            for (const auto& b : o.terms) {
                Exp e(
                    get<0>(a.first) + get<0>(b.first),
                    get<1>(a.first) + get<1>(b.first),
                    get<2>(a.first) + get<2>(b.first)
                );
                r.terms[e] += a.second * b.second;
                if (r.terms[e] == 0)
                    r.terms.erase(e);
            }
        }
        return r;
    }

    Polynomial pow(int n) const {
        Polynomial r(1, jones);
        Polynomial base = *this;
        for (int i = 0; i < n; ++i)
            r = r * base;
        return r;
    }

    operator string() const {
        if (terms.empty())
            return "0";
        string n0 = jones ? "" : "p";
        string n2 = jones ? "" : "r";
        ostringstream out;
        bool first = true;
        for (const auto& kv : terms) {
            int c = kv.second;
            if (c == 0)
                continue;
            int ev = get<0>(kv.first);
            int es = get<1>(kv.first);
            int er = get<2>(kv.first);
            if (first) {
                if (c < 0)
                    out << "-";
                first = false;
            }
            else {
                out << (c < 0 ? " - " : " + ");
            }
            int ac = abs(c);
            string vs;
            if (ev != 0) {
                vs += n0;
                if (ev != 1)
                    vs += superscript(ev);
            }
            if (!jones && es != 0) {
                int qpow = es / 2;
                int srem = es % 2;
                if (srem < 0) {
                    srem += 2;
                    --qpow;
                }
                if (qpow) {
                    vs += "q";
                    if (qpow != 1)
                        vs += superscript(qpow);
                }
                if (srem) {
                    vs += "\u221aq";
                    if (srem != 1)
                        vs += superscript(srem);
                }
            }
            else if (jones && es != 0) {
                vs += "\u221at";
                if (es != 1)
                    vs += superscript(es);
            }
            if (er != 0) {
                vs += n2;
                if (er != 1)
                    vs += superscript(er);
            }
            if (vs.empty()) {
                out << ac;
            }
            else {
                if (ac != 1)
                    out << ac;
                out << vs;
            }
        }
        return out.str();
    }
};

inline ostream& operator<<(ostream& os, const Polynomial& p) {
    return os << string(p);
}

class Fraction {
public:
    Polynomial num;
    Polynomial den;

    Fraction()
        : num(Polynomial(1)),
          den(Polynomial(1)) {}

    Fraction(const Polynomial& n)
        : num(n),
          den(Polynomial(1, n.jones)) {
        normalize();
    }

    Fraction(const Polynomial& n, const Polynomial& d)
        : num(n),
          den(d) {
        normalize();
    }

    Fraction(int c, bool j = false)
        : num(Polynomial(c, j)),
          den(Polynomial(1, j)) {}

    static bool divExactByPplusQ(Polynomial& P) {
        if (P.terms.empty() || P.jones)
            return false;
        int mn = 1000000;
        int mx = -1000000;
        for (const auto& kv : P.terms) {
            int e = get<0>(kv.first);
            mn = min(mn, e);
            mx = max(mx, e);
        }
        if (mx < 0)
            return false;
        int n = mx - mn;
        vector<Polynomial> c(n + 1, Polynomial(false));
        for (const auto& kv : P.terms) {
            int ev = get<0>(kv.first);
            int es = get<1>(kv.first);
            int er = get<2>(kv.first);
            Polynomial mono(false);
            mono.terms[Exp(0, es, er)] = kv.second;
            c[ev - mn] = c[ev - mn] + mono;
        }
        Polynomial qvar = Polynomial::monomial(1, 2, 1, false);
        vector<Polynomial> b(n + 1, Polynomial(false));
        b[n] = c[n];
        for (int i = n - 1; i >= 0; --i)
            b[i] = c[i] - qvar * b[i + 1];
        if (!b[0].terms.empty())
            return false;
        Polynomial quot(false);
        for (int j = 1; j <= n; ++j) {
            for (const auto& kv : b[j].terms) {
                int ev = get<0>(kv.first) + (j - 1) + mn;
                int es = get<1>(kv.first);
                int er = get<2>(kv.first);
                quot.terms[Exp(ev, es, er)] += kv.second;
            }
        }
        for (auto it = quot.terms.begin(); it != quot.terms.end();) {
            if (it->second == 0)
                it = quot.terms.erase(it);
            else
                ++it;
        }
        P = quot;
        return true;
    }

    void normalize() {
        if (num.terms.empty()) {
            den = Polynomial(1, num.jones);
            return;
        }
        if (den.terms.empty())
            return;
        while (!num.jones) {
            Polynomial ntry = num;
            Polynomial dtry = den;
            if (!divExactByPplusQ(ntry) || !divExactByPplusQ(dtry))
                break;
            num = ntry;
            den = dtry;
        }
        int minV = 0, minS = 0, minR = 0;
        bool first = true;
        auto updateMin = [&](const Polynomial& p) {
            for (const auto& kv : p.terms) {
                int ev = get<0>(kv.first);
                int es = get<1>(kv.first);
                int er = get<2>(kv.first);
                if (first) {
                    minV = ev;
                    minS = es;
                    minR = er;
                    first = false;
                }
                else {
                    minV = min(minV, ev);
                    minS = min(minS, es);
                    minR = min(minR, er);
                }
            }
        };
        updateMin(num);
        updateMin(den);
        auto shift = [&](Polynomial& p) {
            Polynomial q(p.jones);
            for (const auto& kv : p.terms) {
                q.terms[Exp(
                    get<0>(kv.first) - minV,
                    get<1>(kv.first) - minS,
                    get<2>(kv.first) - minR
                )] = kv.second;
            }
            p = q;
        };
        shift(num);
        shift(den);
        int g = 0;
        for (const auto& kv : num.terms)
            g = mygcd(g, abs(kv.second));
        for (const auto& kv : den.terms)
            g = mygcd(g, abs(kv.second));
        if (g > 1) {
            for (auto& kv : num.terms)
                kv.second /= g;
            for (auto& kv : den.terms)
                kv.second /= g;
        }
        if (!den.terms.empty() && den.terms.begin()->second < 0) {
            for (auto& kv : num.terms)
                kv.second = -kv.second;
            for (auto& kv : den.terms)
                kv.second = -kv.second;
        }
    }

    Fraction operator+(const Fraction& o) const {
        return Fraction(num * o.den + o.num * den, den * o.den);
    }

    Fraction operator-(const Fraction& o) const {
        return Fraction(num * o.den - o.num * den, den * o.den);
    }

    Fraction operator*(const Fraction& o) const {
        return Fraction(num * o.num, den * o.den);
    }

    Fraction operator*(const Polynomial& p) const {
        return Fraction(num * p, den);
    }

    Fraction operator/(const Fraction& o) const {
        return Fraction(num * o.den, den * o.num);
    }

    Fraction operator/(const Polynomial& p) const {
        return Fraction(num, den * p);
    }

    Fraction inverse() const {
        return Fraction(den, num);
    }

    Fraction pow(int n) const {
        if (n < 0)
            return inverse().pow(-n);
        Fraction r(1, num.jones);
        for (int i = 0; i < n; ++i)
            r = r * (*this);
        return r;
    }

private:
    static bool isCompound(const string& s) {
        return s.find(" + ") != string::npos ||
               s.find(" - ") != string::npos;
    }

    static string parenIfCompound(const string& s) {
        if (isCompound(s))
            return "(" + s + ")";
        return s;
    }

    static bool isPow(const Polynomial& P, int& k) {
        if (P.terms.empty())
            return false;
        Polynomial bin =
            Polynomial::monomial(0, 1, 1, false) +
            Polynomial::monomial(1, 2, 1, false);
        Polynomial pk(1, false);
        for (k = 1; k <= 12; ++k) {
            pk = pk * bin;
            if (pk.terms == P.terms)
                return true;
        }
        return false;
    }

public:
    operator string() const {
        if (num.terms.empty())
            return "0";
        if (num.terms == den.terms)
            return "1";
        int minS_num = 1000000;
        int minS_den = 1000000;
        for (const auto& kv : num.terms)
            minS_num = min(minS_num, get<1>(kv.first));
        for (const auto& kv : den.terms)
            minS_den = min(minS_den, get<1>(kv.first));
        if (minS_den == 1000000)
            minS_den = 0;
        int pull = minS_num - minS_den;
        if (pull > 0 && !num.jones) {
            Polynomial n2(num.jones);
            Polynomial d2(den.jones);
            for (const auto& kv : num.terms) {
                int a = get<0>(kv.first);
                int b = get<1>(kv.first) - pull;
                int c = get<2>(kv.first);
                n2.terms[Exp(a, b, c)] = kv.second;
            }
            for (const auto& kv : den.terms) {
                int a = get<0>(kv.first);
                int b = get<1>(kv.first) - minS_den;
                int c = get<2>(kv.first);
                d2.terms[Exp(a, b, c)] = kv.second;
            }
            if (n2.terms == d2.terms) {
                string pref;
                int qpow = pull / 2;
                int srem = pull % 2;
                if (srem < 0) {
                    srem += 2;
                    --qpow;
                }
                if (qpow) {
                    pref += "q";
                    if (qpow != 1)
                        pref += superscript(qpow);
                }
                if (srem) {
                    pref += "\u221aq";
                    if (srem != 1)
                        pref += superscript(srem);
                }
                return pref.empty() ? "1" : pref;
            }
            bool neg = false;
            if (!n2.terms.empty() && n2.terms.begin()->second < 0) {
                neg = true;
                for (auto& kv : n2.terms)
                    kv.second = -kv.second;
            }
            string pref = neg ? "-" : "";
            int qpow = pull / 2;
            int srem = pull % 2;
            if (srem < 0) {
                srem += 2;
                --qpow;
            }
            if (qpow) {
                pref += "q";
                if (qpow != 1)
                    pref += superscript(qpow);
            }
            if (srem) {
                pref += "\u221aq";
                if (srem != 1)
                    pref += superscript(srem);
            }
            int kd = 0, kn = 0;
            bool dPow = isPow(d2, kd);
            bool nPow = isPow(n2, kn);
            string ns = string(n2);
            string ds = string(d2);
            if (dPow) {
                ds = "(q+p)" + (kd > 1 ? superscript(kd) : "");
            }
            if (nPow) {
                ns = "(q+p)" + (kn > 1 ? superscript(kn) : "");
            }
            if (ds == "1") {
                if (ns == "1")
                    return pref;
                if (nPow)
                    return pref + ns;
                return pref + parenIfCompound(ns);
            }
            return pref + parenIfCompound(ns) + "/" + parenIfCompound(ds);
        }
        int kden = 0, knum = 0;
        bool denPow = isPow(den, kden);
        bool numPow = isPow(num, knum);
        string ns = string(num);
        string ds = string(den);
        if (ns == "0")
            return "0";
        if (ds == "1")
            return ns;
        if (denPow) {
            ds = "(q+p)" + (kden > 1 ? superscript(kden) : "");
        }
        if (numPow) {
            ns = "(q+p)" + (knum > 1 ? superscript(knum) : "");
        }
        if (denPow && numPow) {
            if (knum == kden)
                return "1";
            if (knum > kden) {
                int d = knum - kden;
                return "(q+p)" + (d > 1 ? superscript(d) : "");
            }
            int d = kden - knum;
            return "1/(q+p)" + (d > 1 ? superscript(d) : "");
        }
        return parenIfCompound(ns) + "/" + parenIfCompound(ds);
    }
};

inline ostream& operator<<(ostream& os, const Fraction& f) {
    return os << string(f);
}

class TorusLink {
public:
    int n;
    Fraction fraction;
    static bool vIsP;

    TorusLink(int n_) : n(n_) {
        fraction = compute(n_);
    }

private:
    static map<int, Fraction>& cache() {
        static map<int, Fraction> c;
        return c;
    }

    static Polynomial pPoly() {
        return Polynomial::monomial(vIsP ? 0 : 2, 1, 1, false);
    }

    static Polynomial sPoly() {
        return Polynomial::monomial(1, 1, 1, false);
    }

    static Fraction compute(int n) {
        auto& c = cache();
        auto it = c.find(n);
        if (it != c.end())
            return it->second;

        Fraction result;
        Polynomial p = pPoly();
        Polynomial s =
