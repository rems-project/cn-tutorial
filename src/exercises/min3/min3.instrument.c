int min3(int x, int y, int z)
/*@ ensures return <= x
            && return <= y
            && return <= z;
@*/
{
    if (x <= y && x <= z) {
        return x;
    }
    else if (y <= x && y <= z) {
        return y;
    }
    else {
        return z;
    }
}

int main() {
  int r = min3(1,2,3);
}
