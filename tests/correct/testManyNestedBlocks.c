int main() {
    int x;
    x = 2;
    assert x == 2;

    {{{{{{x = 10;}}}}}}

    if (2 < 3) {
        { x = 100; { x = 10; { x = 9;
            x = 5;
        } x = 11; } x = 666; } x = 777;
        if (0) {

        } else {
            x = 888;
        }
    }

    {{{{{{}}}}}}

    assert x == 888;

    {{{{{{x = 0;}}}}}}

    assert x == 0;

    return 0;
}