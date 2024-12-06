#include<bits/stdc++.h>

using namespace std;

#define endl '\n'

const int MAX = 5290;
int field[MAX];
const int INF = 0x3f3f3f3f;

int main() { 
    cin.tie(0)->sync_with_stdio(0);
    int D,C;
    cin>>D>>C;
    memset(field,INF,sizeof(field));
    vector<int> clubs(C);
    for(int&c : clubs) cin>>c;
    field[0] = 0;
    for(int i=1;i<=D;i++) {
        for(int c : clubs) {
            if(i-c<0) continue;
            field[i] = min(1+field[i-c],field[i]);
        }
    }
    if(field[D]==INF) {
        cout << "Roberta acknowledges defeat." << endl;
    }
    else {
        cout << "Roberta wins in " << field[D] << " strokes." << endl;
    }

	return 0;
}

	
