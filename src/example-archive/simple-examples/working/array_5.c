void a() { int b[] = {0}; }

int main(void)
/*@ trusted; @*/
{
    a();
}