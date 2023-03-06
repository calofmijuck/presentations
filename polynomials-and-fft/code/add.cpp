#include <bits/stdc++.h>
using namespace std;

vector<int> add(vector<int>& f, vector<int>& g) {
    int size = max(f.size(), g.size());
    f.resize(size), g.resize(size);

    vector<int> result(size, 0);
    for (int i = 0; i < size; ++i) {
        result[i] = f[i] + g[i];
    }
    return result;
}

vector<int> multiply(vector<int>& f, vector<int>& g) {
    int size = f.size() + g.size();

    vector<int> result(size, 0);
    for (int i = 0; i < size; ++i) {
        for (int j = 0; j <= i; ++j) {
            result[i] += f[j] * g[i - j];
        }
    }
    return result;
}

int main() {
    ios_base::sync_with_stdio(false); cin.tie(0); cout.tie(0);

    vector<int> f = {1, 1, 1}, g = {-1, 1};

    vector<int> mult = multiply(f, g);
    for (int v : mult) {
        cout << v << ' ';
    }
    return 0;
}
