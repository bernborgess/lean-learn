/**
 *    author:  bernborgess
 *    problem: Good4AndGood5 - lean-learn
 *    created: 10.June.2024 18:37:14
 **/
#include <bits/stdc++.h>

using namespace std;

#define _ cin.tie(0)->sync_with_stdio(0)
#define f first
#define s second
#define pb push_back
#define lob lower_bound  // iterator for first el not less than x
#define upb upper_bound  // iterator for first el bigger than x
#define uset unordered_set
#define umap unordered_map
#define bs bitset
#define sqr(a) (a) * (a)
#define endl '\n'
#define all(v) begin(v), end(v)
#define rall(v) rbegin(v), rend(v)
#define debug(x) cout << #x << " = " << x << endl

typedef long long ll;
typedef pair<int, int> pii;
typedef vector<int> vi;
const int INF = 0x3f3f3f3f;
const ll LINF = 0x3f3f3f3f3f3f3f3fll;

const int MAX = 1000;
int ans[MAX];

int main() {
    _;
    int N;
    cin >> N;
    set<pii> ps, old;
    for (int n = 4; n <= N; n++) {
        old = ps;
        ps.clear();
        if (n % 4 == 0) {
            ps.insert({n / 4, 0});
        }
        for (auto [x, y] : old) {
            if (x > 0) {
                ps.insert({x - 1, y + 1});
            }
        }
        for (auto [x, y] : ps) {
            if (y >= 4) {
                ps.insert({x + 5, y - 4});
            }
        }
        ans[n] = ps.size();
    }
    for (int i = 0; i < N; i++) {
        if (i % 20 == 0) cout << endl;
        cout << ans[i] << ' ';
    }
    cout << endl;
    cout << endl;
    return 0;
}
