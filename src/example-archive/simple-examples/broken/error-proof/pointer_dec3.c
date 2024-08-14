// Crash 

void
pointerdec_crash_3()
{
  int arr[2];
  int *p = &arr[1];
  *(--p); 
}
