// Filed by @lwli11, see https://github.com/rems-project/cerberus/issues/856

#include <limits.h>

int mult_timeout(int a, int b){
  if (a > 0 && b>0 && INT_MAX / b > a){
    return a*b;
  }
  return 0;
}
