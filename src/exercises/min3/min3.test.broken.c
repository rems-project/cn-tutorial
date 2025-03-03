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
        return x;
    }
    else {
        return z;
    }
}
