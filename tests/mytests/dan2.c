int a;
int b;

int main()
    requires 1 == 2,
    ensures a > \result {
  int x;
  int y;
  int z;
  x = x + 1;
  y = x * y;
  z = z + x * y;
  x = +x + !!!y;
  a = 1;
  havoc x;
  x = \old(a);
  {
    x = x + 1;
    int x;
    x = 1092;
    int y;
    y = 191;
  }
  assert(x > y ? x : y);
  y = 1000;
  return (10 + 20) * 9 + x * (2 + y) + z * z * z;
}
