// Provable but post-condition is weaker than we want 

int g;

int
effect()
/*@ accesses g; @*/
/*@ requires 
        take Pre = Owned<int>(&g); @*/
/*@ ensures 
        take Post = Owned<int>(&g); 
        Post == 1i32;  
        return == 1i32; @*/
{
	g = 1;
	return 1;
}

int
main()
/*@ accesses g; @*/
/*@ requires 
        take Pre = Owned<int>(&g); @*/
/*@ ensures 
        take Post = Owned<int>(&g); @*/
/*@ ensures return == 0i32; @*/
{
    int x;
    
    g = 0;
    x = 0;
    if(x && effect())
    	return 1;
    if(g)
    	return 2;
    x = 1;
    if(x && effect()) {
    	if(g != 1)
    		return 3;
    } else {
    	return 4;
    }
    g = 0;
    x = 1;
    if(x || effect()) {
    	if(g)
    		return 5;
    } else {
    	return 6;
    }
    x = 0;
    if(x || effect()) {
    	if(g != 1)
    		return 7;
    } else {
    	return 8;
    } 
    return 0;
}

