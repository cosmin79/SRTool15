int a;
int b;

int sex()
ensures a == \old(b),
ensures b == \old(a)
{
  a = a + b;
  b = a - b;
  a = a - b;
  return 1000;
}


int main(int x, int y)
ensures a == \old(b),
ensures b == \old(a)
{
  int aux;
  aux = sex();

  return 0;
}
