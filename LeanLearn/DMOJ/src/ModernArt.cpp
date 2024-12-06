#include<bits/stdc++.h>

using namespace std;

#define endl '\n'

const int INF = 0x3f3f3f3f;

const int MAX = 102;
bool grid[MAX][MAX];

int main() {
    cin.tie(0)->sync_with_stdio(0);
    int M,N,K;
    cin >> M >> N >> K;
    while (K--) {
        char cr;
        cin >> cr;
        if (cr == 'R') {
            int i; cin >> i; i--;
            for(int j=0;j<N;j++) grid[i][j]^=1;
        } else { // cr == 'C'
            int j; cin >> j; j--;
            for(int i=0;i<M;i++) grid[i][j]^=1;
        }
    }
    int ans = 0;
    for(int i=0;i<M;i++) {
        for(int j=0;j<N;j++) {
            ans += grid[i][j];
        }
    }
    cout << ans << endl;
    return 0;
}

	
