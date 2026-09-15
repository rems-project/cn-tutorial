void a() { 1 / 1; }

int main(void)
/*@ trusted; @*/
{
    a();
}