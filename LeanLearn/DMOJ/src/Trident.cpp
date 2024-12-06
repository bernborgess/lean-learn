#include<bits/stdc++.h>

using namespace std;

#define endl '\n'

int main() { 
    cin.tie(0)->sync_with_stdio(0);
    int t,s,h;
    cin>>t>>s>>h;
    for(int i=0;i<t;i++) {
        for(int j=0;j<3;j++) {
            if(j) for(int k=0;k<s;k++) cout<<' ';
            cout<<'*';
        }
        cout<<endl;
    }
    for(int j=0;j<3;j++) {
        if(j) for(int k=0;k<s;k++) cout<<'*';
        cout<<'*';
    }
    cout<<endl;
    // handle
    for(int i=0;i<h;i++) {
        for(int j=0;j<s+1;j++) cout<<' ';
        cout<<'*'<<endl;
    }
	return 0;
}

	
