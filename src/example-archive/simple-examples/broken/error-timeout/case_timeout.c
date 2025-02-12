// Filed by @lwli11, see https://github.com/rems-project/cerberus/issues/856

#include <limits.h>

int case_timeout(int a, int b){
  if (a==0 || b==0){
    return 0;
  }
  else if (a > 0 && b>0 && INT_MAX / b > a){
    return a*b;
  }
  else if (a>0 && b <0 && b > INT_MIN/a){
    return a*b;
  }
  else if (a<0 && b>0 && a > INT_MIN / b){
    return a*b;
  }
  else if (a<0 && b<0 && b > INT_MAX / a){
    return a*b;
  }
  return 0;
}