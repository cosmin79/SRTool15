
int main() {

	assert (2 || 3);
	assert (3 && 4);
	assert (1 | 0);
	assert (2 ^ 3);
	assert (4 & 4);
	assert (2 == 2);
	assert (2 != 3);
	assert (2 < 3);
	assert (3 <= 3);
	assert (3 > 2);
	assert (2 >= 2);
	assert (1 << 0);
	assert (3 >> 1);

	assert (0 + 1);
	assert (2 - 1);
	assert (1 * 2);

	assert (2 / 2);
	assert (3 % 2);

	assert (+ + 2);
	assert (- - + 2);
	assert (! 0);
	assert (~5);

	return 0;

}