### Example

C program (with a bug).

```C
int min3(int x, int y, int z)
{
	if (x <= y && x <= z) {
		return x;
	} else if (y <= x && x <= z) {
		return y;
	} else {
		return z;
	}
}
```

Specify the expected behavior of this program.

```C
/*@ ensures return <= x
			&& return <= y
			&& return <= z;
@*/
```

Run `cn test` and get a counterexample.

```C
x = 13
y = 4
z = 9
```

Use counterexample to realize and fix the bug.

```C
else if (y <= x && y <= z) // not x <= z
```
