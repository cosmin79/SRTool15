int main() {
    int x;
    x = 5;
    if (2 > 3) {
        int x;
        x = 2;
        assert x == 2;
    }
    assert x == 5;

    return 0;
}