int main() {
    int x;
    x = 2;
    assert x == 2;

    if (2 < 3) {
        havoc x;
        x = 4;
        assert x == 4;
    }
    assert x == 2;

    return 0;
}