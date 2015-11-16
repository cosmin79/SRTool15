int x;

int main() {
    int y;
    y = x;
    x = 2;
    assert x == 2;

    assert y == \old(x);

    return 0;
}