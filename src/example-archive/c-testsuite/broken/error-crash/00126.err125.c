/*
internal error: todo: M_BW_COMPL
cn: internal error, uncaught exception:
    Failure("internal error: todo: M_BW_COMPL")
*/
// Cause: unknown 

int
main()
{
        int x;

        x = 3;
        x = !x;
        x = !x;
        x = ~x;
        x = -x;
        if(x != 2)
                return 1;
        return 0;
}
