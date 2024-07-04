// Examples of failed array initialization. 
// See: https://github.com/rems-project/cerberus/issues/253

int a[][1][1] = {{{8}}};

int b[1][1] = {5, {a}};

