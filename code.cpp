// 入力から面を列挙しようとした
// \(^o^)/

#include <bits/stdc++.h>
using namespace std;
#include <boost/rational.hpp>
#include <boost/multiprecision/cpp_int.hpp>
typedef boost::multiprecision::cpp_int BigInt;
typedef boost::rational<BigInt> BigRational;
#define rep(i,n) for (int i=0;i<(n);i++)
#define rep2(i,a,b) for (int i=(a);i<(b);i++)

#include <boost/geometry.hpp>
#include <boost/geometry/geometries/point_xy.hpp>
#include <boost/geometry/geometries/linestring.hpp>
#include <boost/assign/list_of.hpp>
namespace bg = boost::geometry;

// typedef bg::model::d2::point_xy<BigRational> bgP;
typedef bg::model::d2::point_xy<double> bgP;
typedef bg::model::polygon<bgP> bgG;
typedef bg::model::segment<bgP> bgL;

struct P {
    BigRational x, y;
    P(){}
    P(BigRational _x, BigRational _y) : x(_x), y(_y) {}
    P operator+(const P &p) const {
      return P(this->x + p.x, this->y + p.y);
    }
    P operator-(const P &p) const {
      return P(this->x - p.x, this->y - p.y);
    }
    P operator*(const BigRational &r) const {
      return P(this->x * r, this->y * r);
    }
    bool operator==(const P &p) const {
      return this->x == p.x && this->y == p.y;
    }
    bool operator!=(const P &p) const {
      return !(*this == p);
    }
    friend std::ostream& operator<<(std::ostream& os, const P& p) {
        os << "(" << p.x << "," << p.y << ")";
        return os;
    }
};

struct L {
    P a, b, v;
    L(){}
    L(P _a, P _b) : a(_a), b(_b), v(b - a) {}
    L(BigRational _ax, BigRational _ay, BigRational _bx, BigRational _by) : L(P(_ax, _ay), P(_bx, _by)) {}
    void reverse() {
        swap(a, b);
        v = b - a;
    }
    friend std::ostream& operator<<(std::ostream& os, const L& l) {
        os << "{" << l.a << "," << l.b << "}";
        return os;
    }
};

typedef L S;
typedef vector<P> G;
#define here(g, i) g[i]
#define next(g, i) g[(i + 1) % g.size()]
#define prev(g, i) g[(i - 1 + g.size()) % g.size()]

///////////// 入出力関数 //////////////

// 座標に出てくる分数(分母は省略されているかも)をBigRationalにして返す
BigRational parse(const string& s) {
    stringstream ss(s);
    if (s.find('/') == string::npos) {
        return BigRational(BigInt(s), BigInt(1));
    }
    else {
        string sa, sb;
        getline(ss, sa, '/');
        getline(ss, sb, '/');
        return BigRational(BigInt(sa), BigInt(sb));
    }
}

P readP() {
    string s;
    cin >> s;
    stringstream ss(s);
    string sx;
    getline(ss, sx, ',');
    BigRational x = parse(sx);
    string sy;
    getline(ss, sy, ',');
    BigRational y = parse(sy);
    return P(x, y);
}

L readL() {
    P pa = readP();
    P pb = readP();
    return L(pa, pb);
}

G readG() {
    int n;
    cin >> n;
    G g;
    rep(i, n) g.emplace_back(readP());
    return g;
}

// vector用出力器(G, vector<T> などに使える)
template<class T>
ostream &operator <<(ostream &os, const vector<T> &xs) {
  bool first = true;
  for(const auto &x : xs) {
    if(!first) os << ' ';
    first = false;
    os << x;
  }
  return os;
}

/////////////// 計算 ///////////////

BigRational cross(const P& a, const P& b) {
    return a.x * b.y - a.y * b.x;
}

BigRational dot(const P& a, const P& b) {
    return a.x * b.x + a.y * b.y;
}

BigRational norm(const P& a) {
    return a.x * a.x + a.y * a.y;
}

bool counterClockwiseG(const G& g) {
    // 符号付き面積が正なら反時計回り
    BigRational area;
    rep(i, g.size()) area += cross(here(g, i), next(g, i));
    return area > BigInt("0");
}

int ccw(P a, P b, P c) {
    b = b - a; c = c - a;
    if (cross(b, c) > 0)   return +1;       // counter clockwise
    if (cross(b, c) < 0)   return -1;       // clockwise
    if (dot(b, c) < 0)     return +2;       // c--a--b on line
    if (norm(b) < norm(c)) return -2;       // a--b--c on line
    return 0;
}

P crosspointLL(const L& l, const L& m) {
    BigRational A = cross(l.v, m.v);
    BigRational B = cross(l.v, l.b - m.a);
    return m.a + m.v * (B / A);
}

// gをlで切断し、lの方向ベクトルから見て左側の方を返す
// 直線を逆向きにして呼び出すと多角形の反対側がとれる
G convex_cut(const G& g, const L& l) {
    G h;
    for (int i = 0; i < g.size(); ++i) {
        P p = here(g, i), q = next(g, i);
        if (ccw(l.a, l.b, p) != -1) h.push_back(p);
        if (ccw(l.a, l.b, p) * ccw(l.a, l.b, q) < 0)
            h.push_back(crosspointLL(L(p, q), l));
    }
    return h;
}

P projection(const P& p, const L& l) {
    return l.v * (dot(p, l.v) / norm(l.v));
}

P symmTransPL(P p, L l) {
    p = p - l.a;
    P t = projection(p, l);
    return t * BigRational(BigInt("2")) - p + l.a;
}

G symmTransGL(const G& g, const L& l) {
    G h;
    rep(i, g.size()) {
        h.emplace_back(symmTransPL(g[i], l));
    }
    return h;
}

// 多角形が直線に対してどちら側にあるか
int relationGL(const G& g, const L& l) {
    rep(i, g.size()) {
        // ccwから時計回り or 反時計回りの結果が返ってきたら、それをそのまま返す
        int t = ccw(l.a, l.b, here(g, i));
        if (t == +1 || t == -1) return t;
    }
    return 0;   // ここには来ないはず
}

bool isIntersectSS(const L &s, const L &t) {
  // 端を含む
  return ccw(s.a, s.b, t.a) * ccw(s.a, s.b, t.b) <= 0 &&
    ccw(t.a, t.b, s.a) * ccw(t.a, t.b, s.b) <= 0;
}

double cosLL(const L& s, const L& t) {
    P v1 = s.a - s.b;
    P v2 = t.b - t.a;;
    return (boost::rational_cast<double>(cross(v1, v2)) > 0 ? +1. : -1.)
            * boost::rational_cast<double>(dot(v1, v2))
            / sqrt(boost::rational_cast<double>(norm(v1)))
            / sqrt(boost::rational_cast<double>(norm(v2)));
}

//////// skeletonの複雑化 ////////////////
vector<L> splitSkeleton(const vector<L> &skeleton) {
  vector<L> tmp = skeleton;
  while (true) {
    bool update = false;
    for(int i = 0; i < (int)tmp.size(); ++i) {
      for(int j = i + 1; j < (int)tmp.size(); ++j) {
        // 線分の端を含んで交差判定した時，trueになるのは3通りある
        // 1. 十字形
        // 2. T字型
        // 3. a - b - c 型
        // ここでは1と2だけを気にする必要がある
        if(isIntersectSS(tmp[i], tmp[j])
            && tmp[i].a != tmp[j].a && tmp[i].a != tmp[j].b
            && tmp[i].b != tmp[j].a && tmp[i].b != tmp[j].b) {
          P p = crosspointLL(tmp[i], tmp[j]);
          vector<L> extend;
          if(tmp[i].a != p) extend.push_back(L(tmp[i].a, p));
          if(tmp[i].b != p) extend.push_back(L(tmp[i].b, p));
          if(tmp[j].a != p) extend.push_back(L(tmp[j].a, p));
          if(tmp[j].b != p) extend.push_back(L(tmp[j].b, p));
          if(extend.size() > 2) {
            // vectorから複数要素を消すのむずい
            tmp.erase(tmp.begin() + i);
            tmp.erase(tmp.begin() + j - 1);
            tmp.insert(tmp.end(), extend.begin(), extend.end());
            update = true;
            break;
          }
        }
      }
      if(update) break;
    }
    if(!update) break;
  }
  return tmp;
}

// ///////////// Origami ////////////////
//
// typedef G Facet;
// static const Facet initial_origami = {
//     P(BigRational(BigInt("0")), BigRational(BigInt("0"))),
//     P(BigRational(BigInt("1")), BigRational(BigInt("0"))),
//     P(BigRational(BigInt("1")), BigRational(BigInt("1"))),
//     P(BigRational(BigInt("0")), BigRational(BigInt("1")))
// };

bgG GtobgG(const G& g) {
    bgG bg_g;
    for (auto&& v : g) {
        bg_g.outer().emplace_back(bgP(boost::rational_cast<double>(v.x), boost::rational_cast<double>(v.y)));
    }
    bg_g.outer().emplace_back(bg_g.outer()[0]);
    if (bg::area(bg_g) < 0) {
        bg::reverse(bg_g);
    }
    return bg_g;
}

G bgGtoG(const bgG& bg_g) {
    G g;
    rep(i, bg_g.outer().size() - 1) {
        bgP bg_p = bg_g.outer()[i];
        // ↓BigRatinalに合わせないといけないんだけどそれは……
        g.emplace_back(bg_p.x, bg_p.y);
    }
    return g;
}

bool FindPolygon(const G& g, const vector<bgG>& polygons) {
    bgG bg_g= GtobgG(g);
    for (auto&& bg_h : polygons) {
        if (bg::equals(bg_g, bg_h)) return true;
    }
    return false;
}

// gがhを含むかどうか
bool includes(const bgG& g, const bgG& h) {
    vector<bgG> inters;
    bg::intersection(g, h, inters);
    return bg::area(h) == bg::area(inters[0]);
}

vector<G> enumerateFacets(const vector<L>& skeleton) {
    // vector<G> polygons;
    vector<bgG> bg_polygons;    // 一致判定用にboostのも持っておく
    int m = skeleton.size();
    rep(i, m) {
        G g;
        L e1 = skeleton[i];
        g.emplace_back(e1.a);
        while (true) {
            L e2;
            double max_cos = -100.;
            rep(j, m) {
                if (j == i) continue;
                auto e = skeleton[j];
                if (e.b == e1.b) e.reverse();
                if (e.a == e1.b) {
                    double c = cosLL(e1, e);
                    if (c > max_cos) {
                        max_cos = c;
                        e2 = e;
                    }
                }
            }
            g.emplace_back(e2.a);
            if (e2.b == g[0]) break;
            e1 = e2;
        }
        if (!FindPolygon(g, bg_polygons)) {
            // polygons.emplace_back(g);
            bg_polygons.emplace_back(GtobgG(g));
        }
    }

    // 自分により小さいパーツが含まれるならば自分を除外
    vector<G> polygons;
    rep(i, bg_polygons.size()) {
        bool ok = true;
        rep2(j, i + 1, bg_polygons.size()) {
            if (includes(bg_polygons[i], bg_polygons[j])) {
                ok = false;
                break;
            }
        }
        if (ok) polygons.emplace_back(bgGtoG(bg_polygons[i]));
    }

    return polygons;
}

int main() {
    int n;  // #polygons in silhoutte
    cin >> n;
    vector<G> silhoutte;
    rep(i, n) silhoutte.emplace_back(readG());
    int m; // #edges in skeleton
    cin >> m;
    vector<L> skeleton;
    rep(i, m) skeleton.emplace_back(readL());
    skeleton = splitSkeleton(skeleton);
    m = skeleton.size();

    auto facets = enumerateFacets(skeleton);
    for (auto&& g : facets) {
        cout << g << endl;
    }
}
