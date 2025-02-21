int min3(int x, int y, int z)
{
    if (x <= y && x <= z) {
        return x;
    }
    else if (y <= x && x <= z) {
        return y;
    }
    else {
        return z;
    }
}
