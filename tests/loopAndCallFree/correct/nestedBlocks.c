
int main() {
    int x;
    x = 2;
    assert x == 2;

    if (2 < 3) {
        {
            x = 5;
        }
    }

    assert x == 5;
    return 0;
}