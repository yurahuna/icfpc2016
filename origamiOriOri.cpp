// Origamiクラスを実装した
// 折れるだけ(点の初期位置を復元する方法はわからず)

#include <bits/stdc++.h>
using namespace std;
#include <boost/rational.hpp>
#include <boost/multiprecision/cpp_int.hpp>
typedef boost::multiprecision::cpp_int BigInt;
typedef boost::rational<BigInt> BigRational;
#define rep(i,n) for (int i=0;i<(n);i++)

struct P {
    BigRational x, y;
    P(){}
    P(BigRational _x, BigRational _y) : x(_x), y(_y) {}
    P operator+ (const P& p) {
        return P(this->x + p.x, this->y + p.y);
    }
    P operator- (const P& p) {
        return P(this->x - p.x, this->y - p.y);
    }
    P operator* (const BigRational& r) {
        return P(this->x * r, this->y * r);
    }
    bool operator==(const P& p) {
        return this->x == p.x && this->y == p.y;
    }
    P operator+ (const P& p) const {
        return P(this->x + p.x, this->y + p.y);
    }
    P operator- (const P& p) const {
        return P(this->x - p.x, this->y - p.y);
    }
    P operator* (const BigRational& r) const {
        return P(this->x * r, this->y * r);
    }
    bool operator==(const P& p) const {
        return this->x == p.x && this->y == p.y;
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

///////////// Origami ////////////////

typedef G Facet;
static const Facet initial_origami = {
    P(BigRational(BigInt("0")), BigRational(BigInt("0"))),
    P(BigRational(BigInt("1")), BigRational(BigInt("0"))),
    P(BigRational(BigInt("1")), BigRational(BigInt("1"))),
    P(BigRational(BigInt("0")), BigRational(BigInt("1")))
};

class Origami {
private:
    vector<Facet> facets;
    // 各面に対し、切断されるならば2つに分ける
    void cutFacets(const L& l) {
        vector<Facet> nxt_facets;
        for (auto&& f : facets) {
            G g = convex_cut(f, l);
            nxt_facets.emplace_back(g);
            if (g != f) {
                // 切断されていたら反対側も入れる
                nxt_facets.emplace_back(convex_cut(f, L(l.b, l.a)));
            }
        }
        facets = nxt_facets;
    }
    // 各面に対し、直線の右側にあるならば左側に移動
    void transFacets(const L& l) {
        vector<Facet> nxt_facets;
        for (auto&& f : facets) {
            nxt_facets.emplace_back((relationGL(f, l) == +1 ? symmTransGL(f, l) : f));
        }
        facets = nxt_facets;
    }
public:
    Origami() {
        facets.emplace_back(initial_origami);
    }
    void update(const L& l) {
        cutFacets(l);
        transFacets(l);
    }
    friend std::ostream& operator<<(std::ostream& os, const Origami& o) {
        for (auto&& f : o.facets) os << f << endl;
        os << endl;
        return os;
    }
};

int main() {
    int n;  // #polygons in silhoutte
    cin >> n;
    vector<G> silhoutte;
    rep(i, n) silhoutte.emplace_back(readG());
    int m; // #edges in skeleton
    cin >> m;
    vector<L> skeleton;
    rep(i, m) skeleton.emplace_back(readL());

    // こんな感じで使ってください
    // 横着なのでskeletonを折り目の代わりに使ってますがこれは想定用法ではなさそう
    Origami origami;
    rep(j, m) {
        origami.update(skeleton[j]);
        cout << origami << endl;
    }
}
