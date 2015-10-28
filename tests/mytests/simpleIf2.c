int main() {
  int x;
  int y;

  {
    x = x + y;
    y = x - y;
    x = x - y;
  }

  return x + y;
}
