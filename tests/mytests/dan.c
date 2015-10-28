int a;
int b;

int main(int a, int b)
{
  int x;
  int y;
  int z;
  x = y + z;
  y = x * z;
  z = x * y + x + y + 1;
  x = x * 100 + y * 20 + y * z;
  x = (!!~x);
  return (10 + 20) * 9 + x * (2 + y);
}
