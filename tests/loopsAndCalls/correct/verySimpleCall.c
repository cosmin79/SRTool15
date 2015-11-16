
int f()
  ensures \result == 0
{
  return 0;
}

int main() {

  int y;
  y = f();

  assert y == 0;

  return 0;
}