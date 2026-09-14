int a[] = {{5}};

int main(void)
/*@ trusted; @*/
{
    int x = a[0];
    /*@ assert (x == 5); @*/
}