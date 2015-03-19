#include <sys/types.h>
#include <stdio.h>
#include <string.h>

typedef struct {int64_t type; int32_t refs;} Value;
typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;
typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;
typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;
typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;
typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;
typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;
typedef struct {int64_t type; Value *implFn;} ProtoImpl;
typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;
typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;
List *listCons(Value *x, List *l);
Value *stringValue(char *s);
const int64_t NumberType;
const int64_t KeywordType;
const int64_t SymbolType;
const int64_t StringType;
const int64_t SubStringType;
const int64_t ListType;
const int64_t FunctionType;
List *empty_list;
Value *number_literals();
Value *counts();
Value *types();
Value *symbol_literals();
Value *keyword_literals();
Value *string_literals();
Value *defined_syms();
Value *static_fns();
Value *protocols();


extern void abort();
extern int printf(const char *, ...);
#ifdef REF_COUNT
extern void free(void *);
extern void * malloc(unsigned long);
#else
extern void GC_init();
extern Value * GC_malloc(int64_t);
#endif
typedef Value *(FnType0)(List *);
typedef Value *(FnType1)(List *, Value *);
typedef Value *(FnType2)(List *, Value *, Value *);
typedef Value *(FnType3)(List *, Value *, Value *, Value *);
typedef Value *(FnType4)(List *, Value *, Value *, Value *, Value *);
typedef Value *(FnType5)(List *, Value *, Value *, Value *, Value *, Value *);
typedef Value *(FnType6)(List *, Value *, Value *, Value *, Value *, Value *, Value *);
typedef Value *(FnType7)(List *, Value *, Value *, Value *, Value *, Value *, Value *, Value *);
typedef Value *(FnType8)(List *, Value *, Value *, Value *, Value *, Value *, Value *, Value *, Value *);
typedef Value *(FnType9)(List *, Value *, Value *, Value *, Value *, Value *, Value *, Value *, Value *, Value *);
const int64_t NumberType = 2;
const int64_t KeywordType = 5;
const int64_t SymbolType = 7;
const int64_t StringType = 1;
const int64_t SubStringType = 6;
const int64_t ListType = 4;
const int64_t FunctionType = 3;
List *empty_list = &(List){4,-1,0,0,0};

FILE *outStream;
Number trueVal = {NumberType, -1, 1};
Value* true = (Value *)&trueVal;
Number falseVal = {NumberType, -1, 0};
Value* false = (Value *)&falseVal;
long long malloc_count = 0;
long long free_count = 0;

void incRef(Value *v) {
  if (v == (Value *)0) {
    fprintf(stderr, "why are you incRefing 'null'\n");
     abort();
  } else if (v->refs < -1) {
    fprintf(stderr, "incRefing: %p\n", v);
    abort();
  } else if (v->refs >= 0)
    v->refs++;
  return;
}

void decRef(Value *v) {
  if (v == (Value *)0) {
    fprintf(stderr, "why are you decRefing 'null'\n");
     abort();
  } else if (v->refs < -1) {
    fprintf(stderr, "decRefing: %p\n", v);
  } else if (v->refs == -1) {
    return;
  } else if (v->refs == 0) {
    fprintf(stderr, "decRef already at 0: %p\n", v);
    return;
  } else {
    v->refs--;
    return;
  }
}
Value *my_malloc(int64_t sz) {
  malloc_count++;
#ifdef REF_COUNT
  Value *val = malloc(sz);
#else
  Value *val = GC_malloc(sz);
#endif
  if (sz > sizeof(Value))
    val->refs = 1;
  return(val);
}

typedef struct DirectLL {int64_t type; struct DirectLL *next;} DirectLL;

DirectLL *freeSubStrings = (DirectLL *)0;
SubString *malloc_substring() {
  if (freeSubStrings == (DirectLL *)0)
    return((SubString *)my_malloc(sizeof(SubString)));
  else {
    DirectLL *subStr = freeSubStrings;
    freeSubStrings = subStr->next;
    ((SubString *)subStr)->refs = 1;
    return((SubString *)subStr);
  }
}

int recycledReified = 0;
DirectLL *freeReified[20] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
ReifiedVal *malloc_reified(int implCount) {
  if (implCount > 19 || freeReified[implCount] == (DirectLL *)0)
    return((ReifiedVal *)my_malloc(sizeof(ReifiedVal) + sizeof(Function *) * implCount));
  else {
    recycledReified++;    DirectLL *newReifiedVal = freeReified[implCount];
    freeReified[implCount] = newReifiedVal->next;
    ((ReifiedVal *)newReifiedVal)->refs = 1;
    return((ReifiedVal *)newReifiedVal);
  }
}

int recycledFunction = 0;
DirectLL *freeFunctions[10] = {0,0,0,0,0,0,0,0,0,0};
Function *malloc_function(int arityCount) {
  if (arityCount > 9 || freeFunctions[arityCount] == (DirectLL *)0)
    return((Function *)my_malloc(sizeof(Function) + sizeof(FnArity *) * arityCount));
  else {
    recycledFunction++;
    DirectLL *newFunction = freeFunctions[arityCount];
    freeFunctions[arityCount] = newFunction->next;
    ((Function *)newFunction)->refs = 1;
    return((Function *)newFunction);
  }
}

DirectLL *freeNumbers = (DirectLL *)0;
Number *malloc_number() {
  if (freeNumbers == (DirectLL *)0) {
    Number *numberStructs = (Number *)my_malloc(sizeof(Number) * 100);
    for (int i = 99; i > 0; i--) {
      ((DirectLL *)&numberStructs[i])->next = freeNumbers;
      freeNumbers = (DirectLL *)&numberStructs[i];
    }
    return(numberStructs);
  } else {
    DirectLL *newNumber = freeNumbers;
    freeNumbers = newNumber->next;
    ((Number *)newNumber)->refs = 1;
    return((Number *)newNumber);
  }
}

DirectLL *freeLists = (DirectLL *)0;
List *malloc_list() {
  if (freeLists == (DirectLL *)0) {
    List *listStructs = (List *)my_malloc(sizeof(List) * 500);    for (int i = 499; i > 0; i--) {      ((DirectLL *)&listStructs[i])->next = freeLists;      freeLists = (DirectLL *)&listStructs[i];    }    return(listStructs);  } else {
    DirectLL *newList = freeLists;
    freeLists = newList->next;
    ((List *)newList)->refs = 1;
    return((List *)newList);
  }
}

DirectLL *freeFnAritys = (DirectLL *)0;
FnArity *malloc_fnArity() {
  if (freeFnAritys == (DirectLL *)0)
    return((FnArity *)my_malloc(sizeof(FnArity)));
  else {
    DirectLL *newFnArity = freeFnAritys;
    freeFnAritys = newFnArity->next;
    ((FnArity *)newFnArity)->refs = 1;
    return((FnArity *)newFnArity);
  }
}

void my_free(Value *v) {
  if (v == (Value *)0) {
    fprintf(stderr, "why are you freeing 'null'\n");
     abort();
  } else if (v->refs > 0 || v->refs == -1) {
    return;
  } else if (v->type == 1) {
    v->refs = -10;
    free_count++;
#ifdef REF_COUNT
    free(v);
#endif
  } else if (v->type == 2) {
    v->refs = -10;
    // free_count++;
    ((DirectLL *)v)->next = freeNumbers;
    freeNumbers = (DirectLL *)v;
  } else if (v->type == 3) {
    Function *f = (Function *)v;
    for (int i = 0; i < f->arityCount; i++) {
      decRef((Value *)f->arities[i]);
      my_free((Value *)f->arities[i]);
    }
    v->refs = -10;
    if (f->arityCount < 10) {
      DirectLL *freedList = freeFunctions[f->arityCount];
      freeFunctions[f->arityCount] = (DirectLL *)v;
      ((DirectLL *)v)->next = freedList;
    } else {
      free_count++;
#ifdef REF_COUNT
      free(v);
#endif
    }  } else if (v->type == 4) {
    Value *head = ((List *)v)->head;
    List *tail = ((List *)v)->tail;
    v->refs = -10;
    // free_count++;
    if (head != (Value *)0) {
      decRef(head);
      my_free(head);
    }
    if (tail != (List *)0) {
      decRef((Value *)tail);
      my_free((Value *)tail);
    }
    ((DirectLL *)v)->next = freeLists;
    freeLists = (DirectLL *)v;
  } else if (v->type == 5 ||
             v->type == 6 ||
             v->type == 7) {
    Value *src = ((SubString *)v)->source;
    v->refs = -10;
    // free_count++;
    if (src != (Value *)0) {
      decRef(src);
      my_free(src);
    }
    ((DirectLL *)v)->next = freeSubStrings;
    freeSubStrings = (DirectLL *)v;
  } else if (v->type == 8) {
    FnArity *arity = (FnArity *)v;
    decRef((Value *)arity->closures);
    my_free((Value *)arity->closures);
    v->refs = -10;
    // free_count++;
    ((DirectLL *)v)->next = freeFnAritys;
    freeFnAritys = (DirectLL *)v;
  } else {
    ReifiedVal *rv = (ReifiedVal *)v;
    for (int i = 0; i < rv->implCount; i++) {
      decRef(rv->impls[i]);
      my_free(rv->impls[i]);
    }
    v->refs = -10;
    if (rv->implCount < 20) {
      DirectLL *freedList = freeReified[rv->implCount];
      freeReified[rv->implCount] = (DirectLL *)v;
      ((DirectLL *)v)->next = freedList;
    } else {
      free_count++;
#ifdef REF_COUNT
      free(v);
#endif
    }  }
  // fprintf(stderr, "malloc_count: %lld free_count: %lld\r", malloc_count, free_count);
};
int isTrue(Value *boolVal) {
if (boolVal->type != 2) {
fprintf(outStream, "Invalid boolean value\n");
abort();
}
else
return(((Number *)boolVal)->numVal);
}

Value *findProtoImpl(int64_t type, ProtoImpls *impls) {
int64_t implIndex = 0;
while(implIndex < impls->implCount) {
if (type != impls->impls[implIndex].type) {
implIndex++;
} else
return(impls->impls[implIndex].implFn);
}
return(impls->defaultImpl);
};

FnArity *findFnArity(Value *fnVal, int argCount) {
Function *fn = (Function *)fnVal;
int arityIndex = 0;
FnArity *arity = (FnArity *)fn->arities[arityIndex];
FnArity *variadic = (FnArity *)0;
while(arityIndex < fn->arityCount) {
arity = (FnArity *)fn->arities[arityIndex];
if (arity->variadic) {
variadic = arity;
arityIndex++;
} else if (arity->count != argCount) {
arityIndex++;
} else
return(arity);
}
return(variadic);
};


Value *stringValue(char *s) {
int64_t len = strlen(s);
String *strVal = (String *)my_malloc(sizeof(String) + len + 4);
strVal->type = StringType;
strVal->len = strlen(s);
strncpy(strVal->buffer, s, len);
return((Value *)strVal);
};

Value *symbolValue(char *s) {
SubString *sym = malloc_substring();
sym->type = SymbolType;
sym->buffer = s;
sym->source = (Value *)0;
return((Value *)sym);
};

Value *keywordValue(char *s) {
SubString *kw = malloc_substring();
kw->type = KeywordType;
kw->buffer = s;
kw->source = (Value *)0;
return((Value *)kw);
};

Value *makeSubstr(int64_t len, Value *str, char *subsStart) {
SubString *subStr = malloc_substring();
subStr->type = SubStringType;
subStr->len = len;
subStr->source = str;
incRef(str);
subStr->buffer = subsStart;
return((Value *)subStr);}

Value *numberValue(int64_t n) {
Number *numVal = malloc_number();
numVal->type = NumberType;
numVal->numVal = n;
return((Value *)numVal);
};

List *listCons(Value *x, List *l) {
  if (l->type != ListType) {
    fprintf(stderr, "'cons' requires a list\n");
    abort();
  }
  List *newList = malloc_list();
  newList->type = ListType;
  newList->len = l->len + 1;
  newList->head = (Value *)x;
  newList->tail = l;
  return(newList);
};
ProtoImpls *protoImpls_0;
Value *protoFnImpl_3(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_4 = {8, -1, 1, (List *)0, 0, protoFnImpl_3};
Value *protoFnImpl_5(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_6 = {8, -1, 2, (List *)0, 0, protoFnImpl_5};
Value *protoFnImpl_7(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 3);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType3 *_fn = (FnType3 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2));
}
FnArity protoFnArity_8 = {8, -1, 3, (List *)0, 0, protoFnImpl_7};
Value *protoFnImpl_9(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 4);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType4 *_fn = (FnType4 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3));
}
FnArity protoFnArity_10 = {8, -1, 4, (List *)0, 0, protoFnImpl_9};
Value *protoFnImpl_11(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 5);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType5 *_fn = (FnType5 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3, arg4));
}
FnArity protoFnArity_12 = {8, -1, 5, (List *)0, 0, protoFnImpl_11};
Value *protoFnImpl_13(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 6);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType6 *_fn = (FnType6 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3, arg4, arg5));
}
FnArity protoFnArity_14 = {8, -1, 6, (List *)0, 0, protoFnImpl_13};
Value *protoFnImpl_15(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5, Value *arg6) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 7);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType7 *_fn = (FnType7 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3, arg4, arg5, arg6));
}
FnArity protoFnArity_16 = {8, -1, 7, (List *)0, 0, protoFnImpl_15};
Value *protoFnImpl_17(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5, Value *arg6, Value *arg7) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_0);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 8);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'invoke'\n");
    abort();
}
  FnType8 *_fn = (FnType8 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7));
}
FnArity protoFnArity_18 = {8, -1, 8, (List *)0, 0, protoFnImpl_17};
Function protoFn_1 = {3, -1, "invoke", 8, {&protoFnArity_4,
&protoFnArity_6,
&protoFnArity_8,
&protoFnArity_10,
&protoFnArity_12,
&protoFnArity_14,
&protoFnArity_16,
&protoFnArity_18}};

Number _num_1 = {2, -1, 1};
Number _num_2 = {2, -1, 2};
Number _num_3 = {2, -1, 3};
Number _num_4 = {2, -1, 4};
Number _num_5 = {2, -1, 5};
Number _num_6 = {2, -1, 6};
Number _num_7 = {2, -1, 7};
Number _num_8 = {2, -1, 8};
// forward declaration for 'print-err'
Value *var_19;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_0 = {1, -1, 4,"void"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_1 = {1, -1, 4,"char"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_2 = {1, -1, 6,"char *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[4];} _str_3 = {1, -1, 3,"int"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_4 = {1, -1, 7,"int64_t"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_5 = {1, -1, 52,"typedef struct {int64_t type; int32_t refs;} Value;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_6 = {1, -1, 7,"Value *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[70];} _str_7 = {1, -1, 69,"typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[83];} _str_8 = {1, -1, 82,"typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[99];} _str_9 = {1, -1, 98,"typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[102];} _str_10 = {1, -1, 101,"typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[106];} _str_11 = {1, -1, 105,"typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[108];} _str_12 = {1, -1, 107,"typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[58];} _str_13 = {1, -1, 57,"typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[88];} _str_14 = {1, -1, 87,"typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[89];} _str_15 = {1, -1, 88,"typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"};
Value *var_37 = (Value *)&trueVal;;
Value *var_38 = (Value *)&falseVal;;

// --------- output-to-file --------------
Function fn_39;
Value *arityImpl_40(List *closures, Value *arg0) {
String *arg0Str = (String *)my_malloc(sizeof(String) + ((String *)arg0)->len + 5);
    if (arg0->type == StringType)
      snprintf(arg0Str->buffer, ((String *)arg0)->len + 1, "%s", ((String *)arg0)->buffer);
    else if (arg0->type == SubStringType)
      snprintf(arg0Str->buffer, ((String *)arg0)->len + 1, "%s", ((SubString *)arg0)->buffer);
    else {
      fprintf(stderr, "\ninvalid type for 'output-to-file'\n");
      abort();
    }

    outStream = fopen(arg0Str->buffer, "w");
    return((Value *)&trueVal);
};


// --------- output-to-file main body --------------
Function fn_39 = {3, -1, "output-to-file", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_40}}};


// --------- standard-output --------------
Function fn_42;
Value *arityImpl_43(List *closures) {
outStream = stdout;
    return((Value *)&trueVal);
};


// --------- standard-output main body --------------
Function fn_42 = {3, -1, "standard-output", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_43}}};


// --------- symkey-name --------------
Function fn_45;
Value *arityImpl_46(List *closures, Value *arg0) {
return(stringValue(((SubString *)arg0)->buffer));
};


// --------- symkey-name main body --------------
Function fn_45 = {3, -1, "symkey-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_46}}};


// --------- char-code --------------
Function fn_48;
Value *arityImpl_49(List *closures, Value *arg0) {
if (arg0->type == StringType) {
                  String *s = (String *)arg0;
                  return(numberValue((int)s->buffer[0]));
                } else if (arg0->type == SubStringType) {
                  SubString *s = (SubString *)arg0;
                  return(numberValue((int)s->buffer[0]));
                } else
                  abort();
 };


// --------- char-code main body --------------
Function fn_48 = {3, -1, "char-code", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_49}}};


// --------- symbol --------------
Function fn_51;
Value *arityImpl_52(List *closures, Value *arg0) {
if (arg0->type == StringType) {
                     String *s = (String *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SymbolType;
                     subStr->len = s->len;
                     subStr->source = arg0;
                     incRef(arg0);
                     subStr->buffer = s->buffer;
                     return((Value *)subStr);
                   } else if (arg0->type == SubStringType) {
                     SubString *s = (SubString *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SymbolType;
                     subStr->len = s->len;
                     subStr->source = arg0;
                     incRef(arg0);
                     subStr->buffer = s->buffer;
                     return((Value *)subStr);
                   } else
                     abort();
};


// --------- symbol main body --------------
Function fn_51 = {3, -1, "symbol", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_52}}};


// --------- new-keyword --------------
Function fn_54;
Value *arityImpl_55(List *closures, Value *arg0) {
if (arg0->type == StringType) {
                     String *s = (String *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = KeywordType;
                     subStr->len = s->len;
                     subStr->source = arg0;
                     incRef(arg0);
                     subStr->buffer = s->buffer;
                     return((Value *)subStr);
                   } else if (arg0->type == SubStringType) {
                     SubString *s = (SubString *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SymbolType;
                     subStr->len = s->len;
                     subStr->source = arg0;
                     incRef(arg0);
                     subStr->buffer = s->buffer;
                     return((Value *)subStr);
                   } else
                     abort();
};


// --------- new-keyword main body --------------
Function fn_54 = {3, -1, "new-keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_55}}};


// --------- abort --------------
Function fn_57;
Value *arityImpl_58(List *closures) {
abort();
    return(true);
};


// --------- abort main body --------------
Function fn_57 = {3, -1, "abort", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_58}}};


// --------- get-type --------------
Function fn_60;
Value *arityImpl_61(List *closures, Value *arg0) {
return(numberValue(arg0->type));};


// --------- get-type main body --------------
Function fn_60 = {3, -1, "get-type", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_61}}};


// --------- type= --------------
Function fn_63;
Value *arityImpl_64(List *closures, Value *arg0, Value *arg1) {
if (arg0->type == arg1->type)
                   return(true);
                else
                   return(false);
};


// --------- type= main body --------------
Function fn_63 = {3, -1, "type=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_64}}};


// --------- subs --------------
Function fn_66;
Value *arityImpl_67(List *closures, Value *arg0, Value *arg1) {
int64_t idx = ((Number *)arg1)->numVal;
                   if (arg0->type == StringType) {
                     String *s = (String *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SubStringType;
                     if (idx < s->len) {
                       subStr->len = s->len - idx;
                       subStr->source = arg0;
                       incRef(arg0);
                       subStr->buffer = s->buffer + idx;
                     }
                     else {
                       subStr->len = 0;
                       subStr->source = (Value *)0;
                       subStr->buffer = (char *)0;
                     }
                     return((Value *)subStr);
                   } else if (arg0->type == SubStringType) {
                     SubString *s = (SubString *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SubStringType;
                     if (idx < s->len) {
                       subStr->len = s->len - idx;
                       subStr->source = arg0;
                       incRef(arg0);
                       subStr->buffer = s->buffer + idx;
                     }
                     else {
                       subStr->len = 0;
                       subStr->source = (Value *)0;
                       subStr->buffer = (char *)0;
                     }
                     return((Value *)subStr);
                   } else
                     abort();
};

Value *arityImpl_68(List *closures, Value *arg0, Value *arg1, Value *arg2) {
int64_t idx = ((Number *)arg1)->numVal;
                   int64_t len = ((Number *)arg2)->numVal;
                   if (arg0->type == StringType) {
                     String *s = (String *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SubStringType;
                     if (idx + len <= s->len) {
                       subStr->len = len;
                       subStr->source = arg0;
                       incRef(arg0);
                       subStr->buffer = s->buffer + idx;
                     }
                     else {
                       subStr->len = 0;
                       subStr->source = (Value *)0;
                       subStr->buffer = (char *)0;
                     }
                     return((Value *)subStr);
                   } else if (arg0->type == SubStringType) {
                     SubString *s = (SubString *)arg0;
                     SubString *subStr = malloc_substring();
                     subStr->type = SubStringType;
                     if (idx + len <= s->len) {
                       subStr->len = len;
                       subStr->source = arg0;
                       incRef(arg0);
                       subStr->buffer = s->buffer + idx;
                     }
                     else {
                       subStr->len = 0;
                       subStr->source = (Value *)0;
                       subStr->buffer = (char *)0;
                     }
                     return((Value *)subStr);
                   } else
                     abort();
};


// --------- subs main body --------------
Function fn_66 = {3, -1, "subs", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_67}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_68}}};


// --------- number-str --------------
Function fn_70;
Value *arityImpl_71(List *closures, Value *arg0) {
String *numStr = (String *)my_malloc(sizeof(String) + 10);
    snprintf(numStr->buffer, 9, "%lld", ((Number *)arg0)->numVal);
    numStr->type = StringType;
    numStr->len = strlen(numStr->buffer);
    return((Value *)numStr);
};


// --------- number-str main body --------------
Function fn_70 = {3, -1, "number-str", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_71}}};


// --------- number= --------------
Function fn_73;
Value *arityImpl_74(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      return(false);
   } else if (((Number *)arg0)->numVal != ((Number *)arg1)->numVal)
      return(false);
   else
      return(true);
};


// --------- number= main body --------------
Function fn_73 = {3, -1, "number=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_74}}};


// --------- number-less-than --------------
Function fn_76;
Value *arityImpl_77(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'number-less-than'\n");
      abort();
   } else if (((Number *)arg0)->numVal < ((Number *)arg1)->numVal)
      return(true);
   else
      return(false);
};


// --------- number-less-than main body --------------
Function fn_76 = {3, -1, "number-less-than", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_77}}};


// --------- add-numbers --------------
Function fn_79;
Value *arityImpl_80(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'add-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal + ((Number *)arg1)->numVal));
};


// --------- add-numbers main body --------------
Function fn_79 = {3, -1, "add-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_80}}};


// --------- subtract-numbers --------------
Function fn_82;
Value *arityImpl_83(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'subtract-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal - ((Number *)arg1)->numVal));
};


// --------- subtract-numbers main body --------------
Function fn_82 = {3, -1, "subtract-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_83}}};


// --------- mult-numbers --------------
Function fn_85;
Value *arityImpl_86(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\n*** invalid types for 'mult-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal * ((Number *)arg1)->numVal));
};


// --------- mult-numbers main body --------------
Function fn_85 = {3, -1, "mult-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_86}}};


// --------- rem --------------
Function fn_88;
Value *arityImpl_89(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != NumberType ||
        arg1->type != NumberType) {
      fprintf(outStream, "\ninvalid types for 'rem'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal %
                         ((Number *)arg1)->numVal));
};


// --------- rem main body --------------
Function fn_88 = {3, -1, "rem", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_89}}};

Value *var_91 = (Value *)&(List){4,-1,0,0,0};;

// --------- cons --------------
Function fn_92;
Value *arityImpl_93(List *closures, Value *arg0) {
incRef(arg0);
return((Value *)listCons(arg0, empty_list));
};

Value *arityImpl_94(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
incRef(arg1);
return((Value *)listCons(arg0, (List *)arg1));
};


// --------- cons main body --------------
Function fn_92 = {3, -1, "cons", 2, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_93}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_94}}};


// --------- list-count --------------
Function fn_96;
Value *arityImpl_97(List *closures, Value *arg0) {
if (arg0->type != ListType)
      abort();
    else
      return(numberValue(((List *)arg0)->len));};


// --------- list-count main body --------------
Function fn_96 = {3, -1, "list-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_97}}};


// --------- car --------------
Function fn_99;
Value *arityImpl_100(List *closures, Value *arg0) {
List *lst = (List *)arg0;
    if (arg0->type != ListType) {
      fprintf(stderr, "\n*** 'car' requires a list\n");
      abort();
    } else if (lst->len == 0) {
       fprintf(stderr, "\n*** Cannot get head of empty list!!\n");
       abort();
    } else {
       incRef(lst->head);
       return(lst->head);
    }
};


// --------- car main body --------------
Function fn_99 = {3, -1, "car", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_100}}};


// --------- cdr --------------
Function fn_102;
Value *arityImpl_103(List *closures, Value *arg0) {
List *lst = (List *)arg0;
    if (arg0->type != ListType) {
      fprintf(stderr, "\n*** 'cdr' requires a list\n");
      abort();
    } else if (lst->len == 0) {
       return((Value *)empty_list);
    } else {
       List *tail = ((List *)arg0)->tail;
       tail->len = lst->len - 1;
       incRef((Value *)tail);
       return((Value *)tail);
    }
};


// --------- cdr main body --------------
Function fn_102 = {3, -1, "cdr", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_103}}};


// --------- fn-name --------------
Function fn_105;
Value *arityImpl_106(List *closures, Value *arg0) {
if (arg0->type != FunctionType) {
      fprintf(stderr, "\n*** invalid type for 'fn-name'\n");
      abort();
    } else
      return(stringValue(((Function *)arg0)->name));
};


// --------- fn-name main body --------------
Function fn_105 = {3, -1, "fn-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_106}}};


// --------- char --------------
Function fn_108;
Value *arityImpl_109(List *closures, Value *arg0) {
if (arg0->type != NumberType) {
      fprintf(outStream, "\ninvalid type for 'char'\n");
      abort();
    }
    String *strVal = (String *)my_malloc(sizeof(String) + 2);
    strVal->type = StringType;
    strVal->len = 1;
    strVal->buffer[0] = ((Number *)arg0)->numVal;
    strVal->buffer[1] = 0;
    return((Value *)strVal);
};


// --------- char main body --------------
Function fn_108 = {3, -1, "char", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_109}}};


// --------- str-count --------------
Function fn_111;
Value *arityImpl_112(List *closures, Value *arg0) {
if (arg0->type != StringType && arg0->type != SubStringType ) {
      fprintf(outStream, "\ninvalid type for 'str-count'\n");
      abort();
    }
   return(numberValue(((String *)arg0)->len));
};


// --------- str-count main body --------------
Function fn_111 = {3, -1, "str-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_112}}};


// --------- str= --------------
Function fn_114;
Value *arityImpl_115(List *closures, Value *arg0, Value *arg1) {
if (arg0->type == StringType && arg1->type == StringType) {
      String *s1 = (String *)arg0;
      String *s2 = (String *)arg1;
      if (s1->len == s2->len && strncmp(s1->buffer,s2->buffer,s1->len) == 0)
        return(true);
      else
        return(false);
    } else if (arg0->type == SubStringType && arg1->type == SubStringType) {
      SubString *s1 = (SubString *)arg0;
      SubString *s2 = (SubString *)arg1;
      if (s1->len == s2->len && strncmp(s1->buffer,s2->buffer,s1->len) == 0)
        return(true);
      else
        return(false);
    } else if (arg0->type == StringType &&
               arg1->type == SubStringType) {
      String *s1 = (String *)arg0;
      SubString *s2 = (SubString *)arg1;
      if (s1->len == s2->len && strncmp(s1->buffer,s2->buffer,s1->len) == 0)
        return(true);
      else
        return(false);
    } else if (arg0->type == SubStringType &&
               arg1->type == StringType) {
      SubString *s1 = (SubString *)arg0;
      String *s2 = (String *)arg1;
      if (s1->len == s2->len && strncmp(s1->buffer,s2->buffer,s1->len) == 0)
        return(true);
      else
        return(false);
    } else
       return(false);
};


// --------- str= main body --------------
Function fn_114 = {3, -1, "str=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_115}}};


// --------- symkey= --------------
Function fn_117;
Value *arityImpl_118(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type)
      return(false);
    else {
      SubString *s1 = (SubString *)arg0;
      SubString *s2 = (SubString *)arg1;
      if (s1->type == s2->type && strcmp(s1->buffer, s2->buffer) == 0) {
        return(true);
      } else
        return(false);
    }
};


// --------- symkey= main body --------------
Function fn_117 = {3, -1, "symkey=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_118}}};


// --------- str-malloc --------------
Function fn_120;
Value *arityImpl_121(List *closures, Value *arg0) {
String *strVal = (String *)my_malloc(sizeof(String) + ((Number *)arg0)->numVal);
    strVal->type = StringType;
    strVal->len = 0;
    strVal->buffer[0] = 0;
    return((Value *)strVal);
};


// --------- str-malloc main body --------------
Function fn_120 = {3, -1, "str-malloc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_121}}};


// --------- str-append --------------
Function fn_123;
Value *arityImpl_124(List *closures, Value *arg0, Value *arg1) {
 if (arg0->type != StringType) {
      fprintf(outStream, "\ninvalid type for 'str-append'\n");
      abort();
    }

    String *s1 = (String *)arg0;
    if (arg1->type == StringType) {
      String *s2 = (String *)arg1;
      strncat(s1->buffer, s2->buffer, s2->len);
      s1->len += s2->len;
    } else if (arg1->type == SubStringType) {
      SubString *s2 = (SubString *)arg1;
      strncat(s1->buffer, s2->buffer, s2->len);
      s1->len += s2->len;
    }
    incRef(arg0);
    return(arg0);
};


// --------- str-append main body --------------
Function fn_123 = {3, -1, "str-append", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_124}}};


// --------- pr-err* --------------
Function fn_126;
Value *arityImpl_127(List *closures, Value *arg0) {
if (arg0->type == StringType)
      fprintf(stderr, "%-.*s", (int)((String *)arg0)->len, ((String *)arg0)->buffer);
    else if (arg0->type == SubStringType)
      fprintf(stderr, "%-.*s", (int)((SubString *)arg0)->len, ((SubString *)arg0)->buffer);
    else {
      fprintf(stderr, "\ninvalid type for 'pr-err*'\n");
      abort();
    }
    return(true);
};


// --------- pr-err* main body --------------
Function fn_126 = {3, -1, "pr-err*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_127}}};


// --------- slurp --------------
Function fn_129;
Value *arityImpl_130(List *closures, Value *arg0) {
String *arg0Str = (String *)my_malloc(sizeof(String) + ((String *)arg0)->len + 5);
    if (arg0->type == StringType)
      snprintf(arg0Str->buffer, ((String *)arg0)->len + 1, "%s", ((String *)arg0)->buffer);
    else if (arg0->type == SubStringType)
      snprintf(arg0Str->buffer, ((String *)arg0)->len + 1, "%s", ((SubString *)arg0)->buffer);
    else {
      fprintf(stderr, "\ninvalid type for 'slurp'\n");
      abort();
    }

    FILE *file = fopen(arg0Str->buffer, "r");
    fseek(file, 0, SEEK_END);
    int64_t buffSize = ftell(file);
    fseek(file, 0, SEEK_SET);
    String *strVal = (String *)my_malloc(sizeof(String) + buffSize + 10);
    strVal->type = StringType;
    strVal->len = buffSize;
    fread(strVal->buffer, 1, buffSize, file);
    fclose(file);
    decRef((Value *)arg0Str);
    my_free((Value *)arg0Str);
    return((Value *)strVal);
};


// --------- slurp main body --------------
Function fn_129 = {3, -1, "slurp", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_130}}};


// --------- fn-apply --------------
Function fn_132;
Value *arityImpl_133(List *closures, Value *arg0, Value *arg1) {
List *argList = (List *)arg1;
                     FnArity *_arity = findFnArity(arg0, argList->len);

                     if (_arity == (FnArity *)0) {
                       fprintf(stderr, "\n*** no arity found to apply\n");
                       abort();
                     } else if(_arity->variadic) {
                       FnType1 *_fn = (FnType1 *)_arity->fn;
                       return(_fn(_arity->closures, arg1));
                   } else if (argList->len == 1) {
                       FnType1 *_fn = (FnType1 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       return(_fn(_arity->closures, appArg0));
                   } else if (argList->len == 2) {
                       FnType2 *_fn = (FnType2 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1));
                   } else if (argList->len == 3) {
                       FnType3 *_fn = (FnType3 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2));
                   } else if (argList->len == 4) {
                       FnType4 *_fn = (FnType4 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       argList = argList->tail;
                       Value *appArg3 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2, appArg3));
                   } else if (argList->len == 5) {
                       FnType5 *_fn = (FnType5 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       argList = argList->tail;
                       Value *appArg3 = argList->head;
                       argList = argList->tail;
                       Value *appArg4 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2, appArg3,
                                                    appArg4));
                   } else if (argList->len == 6) {
                       FnType6 *_fn = (FnType6 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       argList = argList->tail;
                       Value *appArg3 = argList->head;
                       argList = argList->tail;
                       Value *appArg4 = argList->head;
                       argList = argList->tail;
                       Value *appArg5 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2, appArg3,
                                                    appArg4, appArg5));
                   } else if (argList->len == 7) {
                       FnType7 *_fn = (FnType7 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       argList = argList->tail;
                       Value *appArg3 = argList->head;
                       argList = argList->tail;
                       Value *appArg4 = argList->head;
                       argList = argList->tail;
                       Value *appArg5 = argList->head;
                       argList = argList->tail;
                       Value *appArg6 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2, appArg3,
                                                    appArg4, appArg5, appArg6));
                   } else if (argList->len == 8) {
                       FnType8 *_fn = (FnType8 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       argList = argList->tail;
                       Value *appArg3 = argList->head;
                       argList = argList->tail;
                       Value *appArg4 = argList->head;
                       argList = argList->tail;
                       Value *appArg5 = argList->head;
                       argList = argList->tail;
                       Value *appArg6 = argList->head;
                       argList = argList->tail;
                       Value *appArg7 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2, appArg3,
                                                    appArg4, appArg5, appArg6, appArg7));
                   } else if (argList->len == 9) {
                       FnType9 *_fn = (FnType9 *)_arity->fn;
                       Value *appArg0 = argList->head;
                       argList = argList->tail;
                       Value *appArg1 = argList->head;
                       argList = argList->tail;
                       Value *appArg2 = argList->head;
                       argList = argList->tail;
                       Value *appArg3 = argList->head;
                       argList = argList->tail;
                       Value *appArg4 = argList->head;
                       argList = argList->tail;
                       Value *appArg5 = argList->head;
                       argList = argList->tail;
                       Value *appArg6 = argList->head;
                       argList = argList->tail;
                       Value *appArg7 = argList->head;
                       argList = argList->tail;
                       Value *appArg8 = argList->head;
                       return(_fn(_arity->closures, appArg0, appArg1, appArg2, appArg3,
                                                    appArg4, appArg5, appArg6, appArg7,
                                                    appArg8));
                     } else {
                       fprintf(outStream, "error in 'fn-apply'\n");
                       abort();
                     }
                   };


// --------- fn-apply main body --------------
Function fn_132 = {3, -1, "fn-apply", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_133}}};


// --------- escape-chars --------------
Function fn_135;
Value *arityImpl_136(List *closures, Value *arg0) {
if (arg0->type == StringType) {
                  String *s = (String *)arg0;
                  String *result = (String *)my_malloc(sizeof(String) + s->len * 2 + 5);
                  char *resultBuffer = result->buffer;
                  int resultIndex = 0;
                  for(int i = 0; i < s->len; i++) {
                    if (s->buffer[i] == 10) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 110;
                    } else if (s->buffer[i] == 34) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 34;
                    } else if (s->buffer[i] == 13) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 114;
                    } else if (s->buffer[i] == 12) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 102;
                    } else if (s->buffer[i] == 8) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 98;
                    } else if (s->buffer[i] == 9) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 116;
                    } else if (s->buffer[i] == 92) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 92;
                    } else
                      resultBuffer[resultIndex++] = s->buffer[i];
                  }
                  resultBuffer[resultIndex] = 0;
                  result->type = StringType;
                  result->len = resultIndex;
                  return((Value *)result);
                } else if (arg0->type == SubStringType) {
                  SubString *s = (SubString *)arg0;
                  String *result = (String *)my_malloc(sizeof(String) + s->len * 2 + 5);
                  char *resultBuffer = result->buffer;
                  int resultIndex = 0;
                  for(int i = 0; i < s->len; i++) {
                    if (s->buffer[i] == 10) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 110;
                    } else if (s->buffer[i] == 34) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 34;
                    } else if (s->buffer[i] == 13) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 114;
                    } else if (s->buffer[i] == 12) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 102;
                    } else if (s->buffer[i] == 8) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 98;
                    } else if (s->buffer[i] == 9) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 116;
                    } else if (s->buffer[i] == 92) {
                      resultBuffer[resultIndex++] = 92;
                      resultBuffer[resultIndex++] = 92;
                    } else
                      resultBuffer[resultIndex++] = s->buffer[i];
                  }
                  resultBuffer[resultIndex] = 0;
                  result->type = StringType;
                  result->len = resultIndex;
                  return((Value *)result);
                } else
                  abort();
 };


// --------- escape-chars main body --------------
Function fn_135 = {3, -1, "escape-chars", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_136}}};


// --------- pr* --------------
Function fn_138;
Value *arityImpl_139(List *closures, Value *arg0) {
if (arg0->type == StringType)
      fprintf(outStream, "%-.*s", (int)((String *)arg0)->len, ((String *)arg0)->buffer);
    else if (arg0->type == SubStringType)
      fprintf(outStream, "%-.*s", (int)((SubString *)arg0)->len, ((SubString *)arg0)->buffer);
    else {
      fprintf(outStream, "\ninvalid type for 'pr*'\n");
      abort();
    }
    return(true);
};


// --------- pr* main body --------------
Function fn_138 = {3, -1, "pr*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_139}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[16];} _str_16 = {1, -1, 15,":match*-one-arg"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[17];} _str_17 = {1, -1, 16,":match*-two-args"};
ProtoImpls *protoImpls_141;
Value *protoFnImpl_144(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_141);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'bippity' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'bippity'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_145 = {8, -1, 1, (List *)0, 0, protoFnImpl_144};
Function protoFn_142 = {3, -1, "bippity", 1, {&protoFnArity_145}};

ProtoImpls *protoImpls_146;
Value *arityImpl_149(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_139(empty_list, (Value *)&_str_16);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *protoFnImpl_150(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_146);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'match*' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'match*'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_151 = {8, -1, 1, (List *)0, 0, protoFnImpl_150};
Value *protoFnImpl_152(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_146);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'match*' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'match*'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_153 = {8, -1, 2, (List *)0, 0, protoFnImpl_152};
Function defaultFn_148 = {3, -1, "match*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_149}}};

Function protoFn_147 = {3, -1, "match*", 2, {&protoFnArity_151,
&protoFnArity_153}};

ProtoImpls *protoImpls_154;
Value *protoFnImpl_157(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_154);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'instance?' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'instance?'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_158 = {8, -1, 2, (List *)0, 0, protoFnImpl_157};
Function protoFn_155 = {3, -1, "instance?", 1, {&protoFnArity_158}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[31];} _str_18 = {1, -1, 30,"*** 'flat-map' not implemented"};
ProtoImpls *protoImpls_159;
Value *arityImpl_162(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_19)->type != 3) {
rslt3 = protoFnImpl_5(empty_list, var_19, (Value *)&_str_18);
} else {
FnArity *arity0 = findFnArity(var_19, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_18);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef((Value *)&_str_18);
varArgs1 = (List *)listCons((Value *)&_str_18, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_19)->name);
  abort();
}
}
Value *rslt4 = arityImpl_58(empty_list);
incRef(rslt4);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};

Value *protoFnImpl_163(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_159);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'flat-map' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'flat-map'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_164 = {8, -1, 2, (List *)0, 0, protoFnImpl_163};
Function defaultFn_161 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_162}}};

Function protoFn_160 = {3, -1, "flat-map", 1, {&protoFnArity_164}};

ProtoImpls *protoImpls_165;

// --------- anon --------------
Function fn_169;
Value *arityImpl_170(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- anon main body --------------
Function fn_169 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_170}}};

Value *arityImpl_168(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_163(empty_list, arg0, (Value *)&fn_169);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_171(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_165);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'flatten' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'flatten'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_172 = {8, -1, 1, (List *)0, 0, protoFnImpl_171};
Function defaultFn_167 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_168}}};

Function protoFn_166 = {3, -1, "flatten", 1, {&protoFnArity_172}};

ProtoImpls *protoImpls_173;
Value *protoFnImpl_176(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_173);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'extract' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'extract'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_177 = {8, -1, 1, (List *)0, 0, protoFnImpl_176};
Function protoFn_174 = {3, -1, "extract", 1, {&protoFnArity_177}};

ProtoImpls *protoImpls_178;
Value *protoFnImpl_181(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_178);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'extend' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'extend'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_182 = {8, -1, 2, (List *)0, 0, protoFnImpl_181};
Function protoFn_179 = {3, -1, "extend", 1, {&protoFnArity_182}};

ProtoImpls *protoImpls_183;
Value *protoFnImpl_186(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_183);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'duplicate' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'duplicate'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_187 = {8, -1, 1, (List *)0, 0, protoFnImpl_186};
Function protoFn_184 = {3, -1, "duplicate", 1, {&protoFnArity_187}};

// forward declaration for 'comprehend'
Value *var_188;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_19 = {1, -1, 26,"*** 'wrap' not implemented"};
Number _num_9 = {2, -1, 0};
ProtoImpls *protoImpls_189;
Value *arityImpl_192(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_19)->type != 3) {
rslt3 = protoFnImpl_5(empty_list, var_19, (Value *)&_str_19);
} else {
FnArity *arity0 = findFnArity(var_19, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_19);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef((Value *)&_str_19);
varArgs1 = (List *)listCons((Value *)&_str_19, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_19)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *protoFnImpl_193(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_189);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'wrap' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'wrap'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_194 = {8, -1, 2, (List *)0, 0, protoFnImpl_193};
Function defaultFn_191 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_192}}};

Function protoFn_190 = {3, -1, "wrap", 1, {&protoFnArity_194}};

ProtoImpls *protoImpls_195;

// --------- anon --------------
Function fn_199;
Value *arityImpl_200(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((var_188)->type != 3) {
rslt4 = protoFnImpl_7(empty_list, var_188, arg0, val0);
} else {
FnArity *arity1 = findFnArity(var_188, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, arg0, val0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(val0);
varArgs2 = (List *)listCons(val0, varArgs2);
incRef(arg0);
varArgs2 = (List *)listCons(arg0, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_188)->name);
  abort();
}
}
incRef(rslt4);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};


// --------- anon --------------
Function fn_201;
Value *arityImpl_202(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((arg0)->type != 3) {
rslt4 = protoFnImpl_3(empty_list, arg0);
} else {
FnArity *arity1 = findFnArity(arg0, 0);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType0 *fn3 = (FnType0 *)arity1->fn;
rslt4 = fn3(arity1->closures);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
Value *rslt5 = protoFnImpl_193(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_198(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_97(empty_list, arg1);
Value *rslt4 = arityImpl_74(empty_list, (Value *)&_num_9, rslt3);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_202;
incRef((Value *)arg0);
arity_5->closures = listCons((Value *)arg0, (List *)arity_5->closures);
Function *fn_201 = malloc_function(1);
fn_201->type = 3;
fn_201->name = "anon";
fn_201->arityCount = 1;
fn_201->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_163(empty_list, arg0, (Value *)fn_201);
incRef(rslt6);
cond0 = rslt6;
decRef((Value *)fn_201);
my_free((Value *)fn_201);
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_200;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_199 = malloc_function(1);
fn_199->type = 3;
fn_199->name = "anon";
fn_199->arityCount = 1;
fn_199->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_163(empty_list, arg0, (Value *)fn_199);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_199);
my_free((Value *)fn_199);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoFnImpl_203(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_195);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'apply*' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'apply*'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_204 = {8, -1, 2, (List *)0, 0, protoFnImpl_203};
Function defaultFn_197 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_198}}};

Function protoFn_196 = {3, -1, "apply*", 1, {&protoFnArity_204}};


// --------- apply --------------
Function fn_205;
Value *arityImpl_206(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = protoFnImpl_203(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- apply main body --------------
Function fn_205 = {3, -1, "apply", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_206}}};


// --------- apply-to --------------
Function fn_208;
Value *arityImpl_209(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt4 = arityImpl_97(empty_list, arg1);
Value *rslt5 = arityImpl_74(empty_list, (Value *)&_num_9, rslt4);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
Value *rslt9;
if((arg0)->type != 3) {
rslt9 = protoFnImpl_3(empty_list, arg0);
} else {
FnArity *arity6 = findFnArity(arg0, 0);
if(arity6 != (FnArity *)0 && !arity6->variadic) {
FnType0 *fn8 = (FnType0 *)arity6->fn;
rslt9 = fn8(arity6->closures);
} else if(arity6 != (FnArity *)0 && arity6->variadic) {
FnType1 *fn8 = (FnType1 *)arity6->fn;
List *varArgs7 = empty_list;
rslt9 = fn8(arity6->closures, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
incRef(rslt9);
cond0 = rslt9;
decRef(rslt9);
my_free(rslt9);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_100(empty_list, arg1);
Value *rslt2 = protoFnImpl_193(empty_list, rslt1, arg0);
Value *rslt3 = protoFnImpl_203(empty_list, rslt2, arg1);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- apply-to main body --------------
Function fn_208 = {3, -1, "apply-to", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_209}}};


// --------- list --------------
Function fn_211;
Value *arityImpl_212(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_211 = {3, -1, "list", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_212}}};

ProtoImpls *protoImpls_214;

// --------- anon --------------
Function fn_218;
Value *arityImpl_219(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt5;
if((val1)->type != 3) {
rslt5 = protoFnImpl_5(empty_list, val1, arg0);
} else {
FnArity *arity2 = findFnArity(val1, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, arg0);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val1)->name);
  abort();
}
}
Value *rslt6 = protoFnImpl_193(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_217(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_219;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_218 = malloc_function(1);
fn_218->type = 3;
fn_218->name = "anon";
fn_218->arityCount = 1;
fn_218->arities[0] = arity_0;
Value *rslt1 = protoFnImpl_163(empty_list, arg0, (Value *)fn_218);
incRef(rslt1);
decRef((Value *)fn_218);
my_free((Value *)fn_218);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_220(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_214);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'map' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'map'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_221 = {8, -1, 2, (List *)0, 0, protoFnImpl_220};
Function defaultFn_216 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_217}}};

Function protoFn_215 = {3, -1, "map", 1, {&protoFnArity_221}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_20 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_222;
Value *arityImpl_225(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt4;
if((var_19)->type != 3) {
rslt4 = protoFnImpl_7(empty_list, var_19, (Value *)&_str_20, rslt0);
} else {
FnArity *arity1 = findFnArity(var_19, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_20, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_20);
varArgs2 = (List *)listCons((Value *)&_str_20, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_19)->name);
  abort();
}
}
Value *rslt5 = arityImpl_58(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_226(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_222);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'name' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'name'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_227 = {8, -1, 1, (List *)0, 0, protoFnImpl_226};
Function defaultFn_224 = {3, -1, "name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_225}}};

Function protoFn_223 = {3, -1, "name", 1, {&protoFnArity_227}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_21 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_228;
Value *arityImpl_231(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt4;
if((var_19)->type != 3) {
rslt4 = protoFnImpl_7(empty_list, var_19, (Value *)&_str_21, rslt0);
} else {
FnArity *arity1 = findFnArity(var_19, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_21, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_21);
varArgs2 = (List *)listCons((Value *)&_str_21, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_19)->name);
  abort();
}
}
Value *rslt5 = arityImpl_58(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_232(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_228);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'string-list' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'string-list'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_233 = {8, -1, 1, (List *)0, 0, protoFnImpl_232};
Function defaultFn_230 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_231}}};

Function protoFn_229 = {3, -1, "string-list", 1, {&protoFnArity_233}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_22 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_234;
Value *arityImpl_237(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt4;
if((var_19)->type != 3) {
rslt4 = protoFnImpl_7(empty_list, var_19, (Value *)&_str_22, rslt0);
} else {
FnArity *arity1 = findFnArity(var_19, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_22, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_22);
varArgs2 = (List *)listCons((Value *)&_str_22, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_19)->name);
  abort();
}
}
Value *rslt5 = arityImpl_58(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_238(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_234);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'serialize' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'serialize'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_239 = {8, -1, 1, (List *)0, 0, protoFnImpl_238};
Function defaultFn_236 = {3, -1, "serialize", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_237}}};

Function protoFn_235 = {3, -1, "serialize", 1, {&protoFnArity_239}};


// --------- list-empty? --------------
Function fn_240;
Value *arityImpl_241(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_97(empty_list, arg0);
Value *rslt1 = arityImpl_74(empty_list, (Value *)&_num_9, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- list-empty? main body --------------
Function fn_240 = {3, -1, "list-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_241}}};


// --------- interpose --------------
Function fn_243;

// --------- anon --------------
Function fn_245;
Value *arityImpl_246(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)val0);
varArgs1 = (List *)listCons((Value *)val0, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *arityImpl_244(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = arityImpl_241(empty_list, arg0);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_100(empty_list, arg0);
Value *rslt2 = arityImpl_103(empty_list, arg0);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_246;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_245 = malloc_function(1);
fn_245->type = 3;
fn_245->name = "anon";
fn_245->arityCount = 1;
fn_245->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_163(empty_list, rslt2, (Value *)fn_245);
Value *rslt5 = arityImpl_94(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_245);
my_free((Value *)fn_245);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- interpose main body --------------
Function fn_243 = {3, -1, "interpose", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_244}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_23 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_24 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_248;
Value *arityImpl_249(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = protoFnImpl_163(empty_list, arg0, (Value *)&protoFn_235);
Value *rslt1 = arityImpl_244(empty_list, rslt0, (Value *)&_str_23);
Value *rslt2 = protoFnImpl_220(empty_list, rslt1, (Value *)&fn_138);
Value *rslt3 = arityImpl_139(empty_list, (Value *)&_str_24);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

// --------- prn main body --------------
Function fn_248 = {3, -1, "prn", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_249}}};


// --------- print --------------
Function fn_251;
Value *arityImpl_252(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_244(empty_list, arg0, (Value *)&_str_23);
Value *rslt1 = protoFnImpl_163(empty_list, rslt0, (Value *)&protoFn_229);
Value *rslt2 = protoFnImpl_220(empty_list, rslt1, (Value *)&fn_138);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

// --------- print main body --------------
Function fn_251 = {3, -1, "print", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_252}}};


// --------- println --------------
Function fn_254;
Value *arityImpl_255(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_244(empty_list, arg0, (Value *)&_str_23);
Value *rslt1 = protoFnImpl_163(empty_list, rslt0, (Value *)&protoFn_229);
Value *rslt2 = protoFnImpl_220(empty_list, rslt1, (Value *)&fn_138);
Value *rslt3 = arityImpl_139(empty_list, (Value *)&_str_24);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

// --------- println main body --------------
Function fn_254 = {3, -1, "println", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_255}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_25 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_257;
Value *arityImpl_258(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_127(empty_list, (Value *)&_str_25);
Value *rslt1 = arityImpl_244(empty_list, arg0, (Value *)&_str_23);
Value *rslt2 = protoFnImpl_163(empty_list, rslt1, (Value *)&protoFn_229);
Value *rslt3 = protoFnImpl_220(empty_list, rslt2, (Value *)&fn_126);
Value *rslt4 = arityImpl_127(empty_list, (Value *)&_str_24);
incRef(rslt4);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};

// --------- print-err main body --------------
Function fn_257 = {3, -1, "print-err", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_258}}};

Value *var_19 = (Value *)&fn_257;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_26 = {1, -1, 21,"'=*' not implemented:"};
ProtoImpls *protoImpls_259;
Value *arityImpl_262(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_26);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_26, varArgs0);
Value *rslt1 = arityImpl_258(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_58(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_263(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_259);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '=*' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to '=*'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_264 = {8, -1, 2, (List *)0, 0, protoFnImpl_263};
Function defaultFn_261 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_262}}};

Function protoFn_260 = {3, -1, "=*", 1, {&protoFnArity_264}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_27 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_265;
Value *arityImpl_268(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_27);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_27, varArgs0);
Value *rslt1 = arityImpl_258(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_58(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_269(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_265);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '<*' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to '<*'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_270 = {8, -1, 2, (List *)0, 0, protoFnImpl_269};
Function defaultFn_267 = {3, -1, "<*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_268}}};

Function protoFn_266 = {3, -1, "<*", 1, {&protoFnArity_270}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_28 = {1, -1, 28,"'count' not implemented for "};
ProtoImpls *protoImpls_271;
Value *protoFnImpl_274(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_271);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'empty?' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'empty?'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_275 = {8, -1, 1, (List *)0, 0, protoFnImpl_274};
Function protoFn_272 = {3, -1, "empty?", 1, {&protoFnArity_275}};

ProtoImpls *protoImpls_276;
Value *protoFnImpl_279(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_276);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'empty' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'empty'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_280 = {8, -1, 1, (List *)0, 0, protoFnImpl_279};
Function protoFn_277 = {3, -1, "empty", 1, {&protoFnArity_280}};

ProtoImpls *protoImpls_281;
Value *protoFnImpl_284(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_281);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'destruct' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'destruct'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_285 = {8, -1, 2, (List *)0, 0, protoFnImpl_284};
Function protoFn_282 = {3, -1, "destruct", 1, {&protoFnArity_285}};

ProtoImpls *protoImpls_286;
Value *arityImpl_289(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_28);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_28, varArgs0);
Value *rslt1 = arityImpl_258(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_58(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_290(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_286);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'count' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'count'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_291 = {8, -1, 1, (List *)0, 0, protoFnImpl_290};
Function defaultFn_288 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_289}}};

Function protoFn_287 = {3, -1, "count", 1, {&protoFnArity_291}};

ProtoImpls *protoImpls_292;
Value *protoFnImpl_295(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_292);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'conj' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'conj'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_296 = {8, -1, 2, (List *)0, 0, protoFnImpl_295};
Function protoFn_293 = {3, -1, "conj", 1, {&protoFnArity_296}};


// --------- not-empty? --------------
Function fn_297;
Value *arityImpl_298(List *closures, Value *arg0) {
Value *cond0;
Value *rslt1 = protoFnImpl_274(empty_list, arg0);
decRef(rslt1);
my_free(rslt1);

if (isTrue(rslt1)) {
decRef(rslt1);
my_free(rslt1);
incRef(var_38);
cond0 = var_38;
} else {
decRef(rslt1);
my_free(rslt1);
incRef(var_37);
cond0 = var_37;
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- not-empty? main body --------------
Function fn_297 = {3, -1, "not-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_298}}};

ProtoImpls *protoImpls_300;
Value *arityImpl_303(List *closures, Value *arg0) {
incRef(var_38);
return(var_38);
};

Value *protoFnImpl_304(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_300);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'seq?' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'seq?'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_305 = {8, -1, 1, (List *)0, 0, protoFnImpl_304};
Function defaultFn_302 = {3, -1, "seq?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_303}}};

Function protoFn_301 = {3, -1, "seq?", 1, {&protoFnArity_305}};

ProtoImpls *protoImpls_306;
Value *protoFnImpl_309(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_306);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'seq' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'seq'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_310 = {8, -1, 1, (List *)0, 0, protoFnImpl_309};
Function protoFn_307 = {3, -1, "seq", 1, {&protoFnArity_310}};

ProtoImpls *protoImpls_311;
Value *protoFnImpl_314(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_311);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'first' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'first'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_315 = {8, -1, 1, (List *)0, 0, protoFnImpl_314};
Function protoFn_312 = {3, -1, "first", 1, {&protoFnArity_315}};

ProtoImpls *protoImpls_316;
Value *protoFnImpl_319(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_316);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'rest' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'rest'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_320 = {8, -1, 1, (List *)0, 0, protoFnImpl_319};
Function protoFn_317 = {3, -1, "rest", 1, {&protoFnArity_320}};


// --------- second --------------
Function fn_321;
Value *arityImpl_322(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_319(empty_list, arg0);
Value *rslt1 = protoFnImpl_314(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- second main body --------------
Function fn_321 = {3, -1, "second", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_322}}};

ProtoImpls *protoImpls_324;
Value *protoFnImpl_327(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_324);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'traverse' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'traverse'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_328 = {8, -1, 2, (List *)0, 0, protoFnImpl_327};
Function protoFn_325 = {3, -1, "traverse", 1, {&protoFnArity_328}};

ProtoImpls *protoImpls_329;
Value *protoFnImpl_332(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_329);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'crush' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'crush'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_333 = {8, -1, 2, (List *)0, 0, protoFnImpl_332};
Function protoFn_330 = {3, -1, "crush", 1, {&protoFnArity_333}};

ProtoImpls *protoImpls_334;
Value *protoFnImpl_337(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_334);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'zero' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'zero'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_338 = {8, -1, 1, (List *)0, 0, protoFnImpl_337};
Function protoFn_335 = {3, -1, "zero", 1, {&protoFnArity_338}};

ProtoImpls *protoImpls_339;
Value *protoFnImpl_342(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_339);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'comp*' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'comp*'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_343 = {8, -1, 2, (List *)0, 0, protoFnImpl_342};
Function protoFn_340 = {3, -1, "comp*", 1, {&protoFnArity_343}};


// --------- comp --------------
Function fn_344;
Value *arityImpl_345(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_274(empty_list, arg1);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = protoFnImpl_342(empty_list, arg0, arg1);
incRef(rslt1);
cond0 = rslt1;
decRef(rslt1);
my_free(rslt1);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- comp main body --------------
Function fn_344 = {3, -1, "comp", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_345}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[24];} _str_29 = {1, -1, 23,"'get' not implemented: "};
SubString _kw_0 = {5, -1, 2, 0, ":m"};
SubString _kw_1 = {5, -1, 2, 0, ":k"};
ProtoImpls *protoImpls_347;
Value *protoFnImpl_350(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_347);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'assoc' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 3);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'assoc'\n");
    abort();
}
  FnType3 *_fn = (FnType3 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2));
}
FnArity protoFnArity_351 = {8, -1, 3, (List *)0, 0, protoFnImpl_350};
Function protoFn_348 = {3, -1, "assoc", 1, {&protoFnArity_351}};

ProtoImpls *protoImpls_352;
Value *arityImpl_355(List *closures, Value *arg0, Value *arg1, Value *arg2) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)(Value *)&_kw_1);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_kw_0);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_0, varArgs0);
incRef((Value *)(Value *)&_str_29);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_29, varArgs0);
Value *rslt1 = arityImpl_258(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_58(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_356(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_352);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'get' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 3);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'get'\n");
    abort();
}
  FnType3 *_fn = (FnType3 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2));
}
FnArity protoFnArity_357 = {8, -1, 3, (List *)0, 0, protoFnImpl_356};
Function defaultFn_354 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_355}}};

Function protoFn_353 = {3, -1, "get", 1, {&protoFnArity_357}};

ProtoImpls *protoImpls_358;
Value *protoFnImpl_361(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_358);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'keys' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'keys'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_362 = {8, -1, 1, (List *)0, 0, protoFnImpl_361};
Function protoFn_359 = {3, -1, "keys", 1, {&protoFnArity_362}};

ProtoImpls *protoImpls_363;
Value *protoFnImpl_366(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_363);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'vals' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'vals'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_367 = {8, -1, 1, (List *)0, 0, protoFnImpl_366};
Function protoFn_364 = {3, -1, "vals", 1, {&protoFnArity_367}};


// --------- not --------------
Function fn_368;
Value *arityImpl_369(List *closures, Value *arg0) {
Value *cond0;

if (isTrue(arg0)) {
decRef(arg0);
my_free(arg0);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(arg0);
my_free(arg0);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- not main body --------------
Function fn_368 = {3, -1, "not", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_369}}};


// --------- and --------------
Function fn_371;
Value *arityImpl_372(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt1 = protoFnImpl_274(empty_list, arg0);
decRef(rslt1);
my_free(rslt1);

if (isTrue(rslt1)) {
decRef(rslt1);
my_free(rslt1);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt1);
my_free(rslt1);
Value *rslt2 = protoFnImpl_314(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = protoFnImpl_319(empty_list, arg0);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_371);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_371, varArgs4);
Value *rslt5 = arityImpl_206(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
} else {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- and main body --------------
Function fn_371 = {3, -1, "and", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_372}}};


// --------- or --------------
Function fn_374;
Value *arityImpl_375(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt4 = protoFnImpl_274(empty_list, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt5 = protoFnImpl_314(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = protoFnImpl_319(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)(Value *)&fn_374);
varArgs2 = (List *)listCons((Value *)(Value *)&fn_374, varArgs2);
Value *rslt3 = arityImpl_206(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt3);
my_free(rslt3);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- or main body --------------
Function fn_374 = {3, -1, "or", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_375}}};


// --------- = --------------
Function fn_377;
Value *arityImpl_378(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_263(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_379(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg1);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_314(empty_list, arg1);
Value *rslt5 = protoFnImpl_263(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_369(empty_list, rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_290(empty_list, arg1);
Value *rslt8 = arityImpl_74(empty_list, (Value *)&_num_1, rslt7);
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt8);
my_free(rslt8);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
incRef((Value *)(Value *)&fn_377);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_377, varArgs1);
Value *rslt2 = arityImpl_206(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt2);
my_free(rslt2);
}
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- = main body --------------
Function fn_377 = {3, -1, "=", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_378}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_379}}};


// --------- < --------------
Function fn_381;
Value *arityImpl_382(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_269(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_383(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg1);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_314(empty_list, arg1);
Value *rslt5 = protoFnImpl_269(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_369(empty_list, rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_290(empty_list, arg1);
Value *rslt8 = arityImpl_74(empty_list, (Value *)&_num_1, rslt7);
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt8);
my_free(rslt8);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
incRef((Value *)(Value *)&fn_381);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_381, varArgs1);
Value *rslt2 = arityImpl_206(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt2);
my_free(rslt2);
}
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- < main body --------------
Function fn_381 = {3, -1, "<", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_382}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_383}}};


// --------- list** --------------
Function fn_385;
Value *arityImpl_386(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_274(empty_list, arg1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = protoFnImpl_314(empty_list, arg1);
Value *rslt2 = protoFnImpl_319(empty_list, arg1);
Value *rslt3 = arityImpl_386(closures, rslt1, rslt2);
Value *rslt4 = arityImpl_94(empty_list, arg0, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- list** main body --------------
Function fn_385 = {3, -1, "list**", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_386}}};


// --------- list* --------------
Function fn_388;
Value *arityImpl_389(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = arityImpl_386(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- list* main body --------------
Function fn_388 = {3, -1, "list*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_389}}};


// --------- reduce --------------
Function fn_391;
Value *arityImpl_392(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt10 = protoFnImpl_274(empty_list, arg0);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
incRef(arg1);
cond0 = arg1;
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_314(empty_list, arg0);
Value *rslt2 = protoFnImpl_319(empty_list, arg0);
Value *rslt6;
if((arg2)->type != 3) {
rslt6 = protoFnImpl_7(empty_list, arg2, arg1, rslt1);
} else {
FnArity *arity3 = findFnArity(arg2, 2);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType2 *fn5 = (FnType2 *)arity3->fn;
rslt6 = fn5(arity3->closures, arg1, rslt1);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(rslt1);
varArgs4 = (List *)listCons(rslt1, varArgs4);
incRef(arg1);
varArgs4 = (List *)listCons(arg1, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg2)->name);
  abort();
}
}
Value *cond7;
Value *rslt9 = protoFnImpl_274(empty_list, rslt2);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(rslt6);
cond7 = rslt6;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt8 = arityImpl_392(closures, rslt2, rslt6, arg2);
incRef(rslt8);
cond7 = rslt8;
decRef(rslt8);
my_free(rslt8);
}
incRef(cond7);
cond0 = cond7;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt6);
my_free(rslt6);
decRef(cond7);
my_free(cond7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- reduce main body --------------
Function fn_391 = {3, -1, "reduce", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_392}}};


// --------- filter --------------
Function fn_394;
Value *arityImpl_395(List *closures, Value *arg0, Value *arg1) {
List *l = (List *)arg0;
      if (arg0->type != ListType) {
         fprintf(stderr, "'filter' is only defined for 'List' values\n");
         abort();
      }

      if (l->len == 0)
        return((Value *)empty_list);
      else {
        List *head = empty_list;
        List *tail;
        for(Value *x = l->head; x != (Value *)0; l = l->tail, x = l->head) {
          Value *y;
          if(arg1->type != 3) {
            y = protoFnImpl_5(empty_list, arg1, x);
          } else {
            FnArity *arity2 = findFnArity(arg1, 1);
            if(arity2 != (FnArity *)0 && !arity2->variadic) {
              FnType1 *fn4 = (FnType1 *)arity2->fn;
              y = fn4(arity2->closures, x);
            } else if(arity2 != (FnArity *)0 && arity2->variadic) {
              FnType1 *fn4 = (FnType1 *)arity2->fn;
              List *varArgs3 = empty_list;
              incRef(x);
              varArgs3 = (List *)listCons(x, varArgs3);
              y = fn4(arity2->closures, (Value *)varArgs3);
              incRef(y);
              decRef((Value *)varArgs3);
              my_free((Value *)varArgs3);
              decRef(y);
            } else {
              fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
              abort();
            }
          }

          // 'y' is the filter boolean value

          if (isTrue(y)) {
            if (head == empty_list) {
              // if we haven't started the new list yet
              head = malloc_list();
              head->type = ListType;
              head->len = 1;
              head->head = x;
              incRef(x);
              head->tail = empty_list;
              tail = head;
            } else {
              // otherwise, append to tail of list
              List *new_tail = malloc_list();
              new_tail->type = ListType;
              new_tail->len = 1;
              new_tail->head = x;
              incRef(x);
              new_tail->tail = empty_list;
              tail->tail = new_tail;
              tail = new_tail;
              head->len++;
            }
          }
        }
        return((Value *)head);
      }
};


// --------- filter main body --------------
Function fn_394 = {3, -1, "filter", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_395}}};


// --------- remove --------------
Function fn_397;

// --------- anon --------------
Function fn_399;
Value *arityImpl_400(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((val0)->type != 3) {
rslt4 = protoFnImpl_5(empty_list, val0, arg0);
} else {
FnArity *arity1 = findFnArity(val0, 1);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
rslt4 = fn3(arity1->closures, arg0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(arg0);
varArgs2 = (List *)listCons(arg0, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val0)->name);
  abort();
}
}
Value *rslt5 = arityImpl_369(empty_list, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_398(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_400;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_399 = malloc_function(1);
fn_399->type = 3;
fn_399->name = "anon";
fn_399->arityCount = 1;
fn_399->arities[0] = arity_0;
Value *rslt1 = arityImpl_395(empty_list, arg0, (Value *)fn_399);
incRef(rslt1);
decRef((Value *)fn_399);
my_free((Value *)fn_399);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- remove main body --------------
Function fn_397 = {3, -1, "remove", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_398}}};


// --------- reverse --------------
Function fn_402;
Value *arityImpl_403(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_279(empty_list, arg0);
Value *rslt1 = arityImpl_392(empty_list, arg0, rslt0, (Value *)&protoFn_293);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- reverse main body --------------
Function fn_402 = {3, -1, "reverse", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_403}}};


// --------- identity --------------
Function fn_405;
Value *arityImpl_406(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_405 = {3, -1, "identity", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_406}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_30 = {1, -1, 5,"<Fn: "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_31 = {1, -1, 1,">"};

// --------- string-list_impl --------------
Function fn_408;
Value *arityImpl_409(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_106(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_31);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_31, varArgs1);
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
incRef((Value *)(Value *)&_str_30);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_30, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_408 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_409}}};


// --------- zero_impl --------------
Function fn_410;
Value *arityImpl_411(List *closures, Value *arg0) {
incRef((Value *)&fn_405);
return((Value *)&fn_405);
};


// --------- zero_impl main body --------------
Function fn_410 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_411}}};


// --------- comp*_impl --------------
Function fn_412;

// --------- anon --------------
Function fn_414;

// --------- anon --------------
Function fn_416;
Value *arityImpl_417(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((arg1)->type != 3) {
rslt3 = protoFnImpl_5(empty_list, arg1, arg0);
} else {
FnArity *arity0 = findFnArity(arg1, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg0);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- anon main body --------------
Function fn_416 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_417}}};

Value *arityImpl_415(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
incRef((Value *)val1);
varArgs2 = (List *)listCons((Value *)val1, varArgs2);
Value *rslt3 = arityImpl_206(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
Value *rslt5 = arityImpl_392(empty_list, val0, rslt3, (Value *)&fn_416);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_413(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_415;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_414 = malloc_function(1);
fn_414->type = 3;
fn_414->name = "anon";
fn_414->arityCount = 1;
fn_414->arities[0] = arity_0;
incRef((Value *)fn_414);
decRef((Value *)fn_414);
my_free((Value *)fn_414);
return((Value *)fn_414);
};


// --------- comp*_impl main body --------------
Function fn_412 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_413}}};


// --------- apply*_impl --------------
Function fn_418;
Value *arityImpl_419(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_274(empty_list, arg1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
Value *rslt9;
if((arg0)->type != 3) {
rslt9 = protoFnImpl_3(empty_list, arg0);
} else {
FnArity *arity6 = findFnArity(arg0, 0);
if(arity6 != (FnArity *)0 && !arity6->variadic) {
FnType0 *fn8 = (FnType0 *)arity6->fn;
rslt9 = fn8(arity6->closures);
} else if(arity6 != (FnArity *)0 && arity6->variadic) {
FnType1 *fn8 = (FnType1 *)arity6->fn;
List *varArgs7 = empty_list;
rslt9 = fn8(arity6->closures, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
incRef(rslt9);
cond0 = rslt9;
decRef(rslt9);
my_free(rslt9);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = protoFnImpl_314(empty_list, arg1);
Value *rslt2 = protoFnImpl_319(empty_list, arg1);
Value *rslt3 = arityImpl_386(empty_list, rslt1, rslt2);
Value *rslt4 = arityImpl_133(empty_list, arg0, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- apply*_impl main body --------------
Function fn_418 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_419}}};


// --------- =*_impl --------------
Function fn_420;
Value *arityImpl_421(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_74(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_420 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_421}}};


// --------- <*_impl --------------
Function fn_422;
Value *arityImpl_423(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_77(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- <*_impl main body --------------
Function fn_422 = {3, -1, "<*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_423}}};


// --------- string-list_impl --------------
Function fn_424;
Value *arityImpl_425(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_71(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_424 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_425}}};


// --------- any? --------------
Function fn_426;
Value *arityImpl_427(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg1);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_314(empty_list, arg1);
Value *rslt8;
if((arg0)->type != 3) {
rslt8 = protoFnImpl_5(empty_list, arg0, rslt4);
} else {
FnArity *arity5 = findFnArity(arg0, 1);
if(arity5 != (FnArity *)0 && !arity5->variadic) {
FnType1 *fn7 = (FnType1 *)arity5->fn;
rslt8 = fn7(arity5->closures, rslt4);
} else if(arity5 != (FnArity *)0 && arity5->variadic) {
FnType1 *fn7 = (FnType1 *)arity5->fn;
List *varArgs6 = empty_list;
incRef(rslt4);
varArgs6 = (List *)listCons(rslt4, varArgs6);
rslt8 = fn7(arity5->closures, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
decRef(rslt4);
my_free(rslt4);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt1 = protoFnImpl_319(empty_list, arg1);
Value *rslt2 = arityImpl_427(closures, arg0, rslt1);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- any? main body --------------
Function fn_426 = {3, -1, "any?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_427}}};

ProtoImpls *protoImpls_429;
Value *protoFnImpl_432(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_429);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '.v' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to '.v'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_433 = {8, -1, 1, (List *)0, 0, protoFnImpl_432};
Function protoFn_430 = {3, -1, ".v", 1, {&protoFnArity_433}};

// forward declaration for 'ZipList'
Value *var_434;

Number _num_10 = {2, -1, 10};
SubString _kw_2 = {5, -1, 4, 0, ":nil"};

// --------- instance?_impl --------------
Function fn_435;
Value *arityImpl_436(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_61(empty_list, arg1);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_435 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_436}}};

Value *protoImpl_437(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_438 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_437}}};


// --------- invoke_impl --------------
Function fn_439;

// --------- apply*_impl --------------
Function fn_441;

// --------- anon --------------
Function fn_443;
Value *arityImpl_444(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = protoFnImpl_274(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_kw_2);
cond0 = (Value *)&_kw_2;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = protoFnImpl_314(empty_list, arg0);
incRef(rslt1);
cond0 = rslt1;
decRef(rslt1);
my_free(rslt1);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- anon main body --------------
Function fn_443 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_444}}};

Value *arityImpl_442(List *closures, Value *arg0, Value *arg1) {
Value *val4 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt9 = arityImpl_427(empty_list, (Value *)&protoFn_272, arg1);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt2 = protoFnImpl_220(empty_list, arg1, (Value *)&fn_443);
Value *rslt3 = protoFnImpl_220(empty_list, arg1, (Value *)&protoFn_317);
List *varArgs5 = empty_list;
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
incRef((Value *)val4);
varArgs5 = (List *)listCons((Value *)val4, varArgs5);
Value *rslt6 = arityImpl_206(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_203(empty_list, arg0, rslt3);
Value *rslt8 = arityImpl_94(empty_list, rslt6, rslt7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoImpl_445(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_446 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_445}}};


// --------- .v_impl --------------
Function fn_447;
Value *arityImpl_448(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_449(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_450 = {3, -1, ".v", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_449}}};

Value *arityImpl_440(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_442;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_441 = malloc_function(1);
fn_441->type = 3;
fn_441->name = "apply*_impl";
fn_441->arityCount = 1;
fn_441->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_448;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_447 = malloc_function(1);
fn_447->type = 3;
fn_447->name = ".v_impl";
fn_447->arityCount = 1;
fn_447->arities[0] = arity_1;
Value *reified_2 = (Value *)malloc_reified(2);
((ReifiedVal *)reified_2)->type = 10;
((ReifiedVal *)reified_2)->implCount = 2;
((ReifiedVal *)reified_2)->impls[0] = (Value *)fn_441;
incRef((Value *)fn_441);
((ReifiedVal *)reified_2)->impls[1] = (Value *)fn_447;
incRef((Value *)fn_447);
incRef(reified_2);
decRef((Value *)fn_441);
my_free((Value *)fn_441);
decRef((Value *)fn_447);
my_free((Value *)fn_447);
decRef(reified_2);
my_free(reified_2);
return(reified_2);
};


// --------- invoke_impl main body --------------
Function fn_439 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_440}}};

Value *protoImpl_451(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_452 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_451}}};

ReifiedVal reified_453 = {9, -1, 2, {(Value *)&fn_435, (Value *)&fn_439}};
Value *var_434 = (Value *)&reified_453;

// --------- partial --------------
Function fn_454;

// --------- anon --------------
Function fn_456;
Value *arityImpl_457(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
incRef((Value *)val1);
varArgs2 = (List *)listCons((Value *)val1, varArgs2);
Value *rslt3 = arityImpl_345(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val0);
varArgs4 = (List *)listCons((Value *)val0, varArgs4);
Value *rslt5 = arityImpl_206(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_455(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_457;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_456 = malloc_function(1);
fn_456->type = 3;
fn_456->name = "anon";
fn_456->arityCount = 1;
fn_456->arities[0] = arity_0;
incRef((Value *)fn_456);
decRef((Value *)fn_456);
my_free((Value *)fn_456);
return((Value *)fn_456);
};

// --------- partial main body --------------
Function fn_454 = {3, -1, "partial", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_455}}};


// --------- comprehend --------------
Function fn_459;

// --------- anon --------------
Function fn_461;
Value *arityImpl_462(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_94(empty_list, arg1, arg0);
Value *rslt3 = arityImpl_403(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val1);
varArgs4 = (List *)listCons((Value *)val1, varArgs4);
Value *rslt5 = arityImpl_206(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = protoFnImpl_193(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};


// --------- anon --------------
Function fn_463;

// --------- anon --------------
Function fn_465;
Value *arityImpl_466(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_94(empty_list, arg1, arg0);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)val1);
varArgs3 = (List *)listCons((Value *)val1, varArgs3);
Value *rslt4 = arityImpl_455(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_163(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_464(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_466;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_465 = malloc_function(1);
fn_465->type = 3;
fn_465->name = "anon";
fn_465->arityCount = 1;
fn_465->arities[0] = arity_0;
incRef((Value *)fn_465);
decRef((Value *)fn_465);
my_free((Value *)fn_465);
return((Value *)fn_465);
};


// --------- anon main body --------------
Function fn_463 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_464}}};


// --------- anon --------------
Function fn_467;
Value *arityImpl_468(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt5;
if((val1)->type != 3) {
rslt5 = protoFnImpl_5(empty_list, val1, arg0);
} else {
FnArity *arity2 = findFnArity(val1, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, arg0);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val1)->name);
  abort();
}
}
Value *rslt6 = protoFnImpl_193(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_460(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt16 = protoFnImpl_274(empty_list, arg1);
decRef(rslt16);
my_free(rslt16);

if (isTrue(rslt16)) {
decRef(rslt16);
my_free(rslt16);
Value *rslt20;
if((arg0)->type != 3) {
rslt20 = protoFnImpl_3(empty_list, arg0);
} else {
FnArity *arity17 = findFnArity(arg0, 0);
if(arity17 != (FnArity *)0 && !arity17->variadic) {
FnType0 *fn19 = (FnType0 *)arity17->fn;
rslt20 = fn19(arity17->closures);
} else if(arity17 != (FnArity *)0 && arity17->variadic) {
FnType1 *fn19 = (FnType1 *)arity17->fn;
List *varArgs18 = empty_list;
rslt20 = fn19(arity17->closures, (Value *)varArgs18);
decRef((Value *)varArgs18);
my_free((Value *)varArgs18);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
incRef(rslt20);
cond0 = rslt20;
decRef(rslt20);
my_free(rslt20);
} else {
decRef(rslt16);
my_free(rslt16);
Value *rslt1 = protoFnImpl_314(empty_list, arg1);
Value *rslt2 = protoFnImpl_319(empty_list, arg1);
Value *rslt3 = arityImpl_403(empty_list, rslt2);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_462;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
incRef((Value *)rslt1);
arity_4->closures = listCons((Value *)rslt1, (List *)arity_4->closures);
Function *fn_461 = malloc_function(1);
fn_461->type = 3;
fn_461->name = "anon";
fn_461->arityCount = 1;
fn_461->arities[0] = arity_4;
Value *rslt6 = arityImpl_392(empty_list, rslt3, (Value *)fn_461, (Value *)&fn_463);
Value *cond7;
Value *rslt11 = protoFnImpl_290(empty_list, arg1);
Value *rslt12 = arityImpl_74(empty_list, (Value *)&_num_1, rslt11);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
Value *rslt13 = protoFnImpl_314(empty_list, arg1);
FnArity *arity_14 = malloc_fnArity();
arity_14->type = 8;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_468;
incRef((Value *)arg0);
arity_14->closures = listCons((Value *)arg0, (List *)arity_14->closures);
incRef((Value *)rslt1);
arity_14->closures = listCons((Value *)rslt1, (List *)arity_14->closures);
Function *fn_467 = malloc_function(1);
fn_467->type = 3;
fn_467->name = "anon";
fn_467->arityCount = 1;
fn_467->arities[0] = arity_14;
Value *rslt15 = protoFnImpl_163(empty_list, rslt13, (Value *)fn_467);
incRef(rslt15);
cond7 = rslt15;
decRef(rslt13);
my_free(rslt13);
decRef((Value *)fn_467);
my_free((Value *)fn_467);
decRef(rslt15);
my_free(rslt15);
} else {
decRef(rslt12);
my_free(rslt12);
List *varArgs8 = empty_list;
incRef((Value *)var_91);
varArgs8 = (List *)listCons((Value *)var_91, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_455(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_163(empty_list, rslt1, rslt9);
incRef(rslt10);
cond7 = rslt10;
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);
}
incRef(cond7);
cond0 = cond7;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef((Value *)fn_461);
my_free((Value *)fn_461);
decRef(rslt6);
my_free(rslt6);
decRef(cond7);
my_free(cond7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comprehend main body --------------
Function fn_459 = {3, -1, "comprehend", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_460}}};

Value *var_188 = (Value *)&fn_459;

// --------- list-concat --------------
Function fn_469;
Value *arityImpl_470(List *closures, Value *arg0) {
 List *ls = (List *)arg0;

  if (ls->len == 0) {
    return((Value *)empty_list);
  }
  else if (ls->len == 1) {
    incRef(ls->head);
    return(ls->head);
  }
  else {
    List *head = empty_list;
    List *tail;
    for (; ls != (List *)0; ls = ls->tail) {
      List *l = (List *)ls->head;
      Value *x;
      for(; l != (List *)0 && l->head != (Value *)0; l = l->tail) {
        x = l->head;
        if (head == empty_list) {
          // if we haven't started the new list yet
          head = malloc_list();
          head->type = ListType;
          head->len = 1;
          head->head = x;
          incRef(x);
          head->tail = empty_list;
          tail = head;
        } else {
          // otherwise, append to tail of list
          List *new_tail = malloc_list();
          new_tail->type = ListType;
          new_tail->len = 1;
          new_tail->head = x;
          incRef(x);
          new_tail->tail = empty_list;
          tail->tail = new_tail;
          tail = new_tail;
          head->len++;
        }
      }
    }
    return((Value *)head);
    }
};


// --------- list-concat main body --------------
Function fn_469 = {3, -1, "list-concat", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_470}}};


// --------- list=* --------------
Function fn_472;

// --------- anon --------------
Function fn_474;
Value *arityImpl_475(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_314(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- anon main body --------------
Function fn_474 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_475}}};

Value *arityImpl_473(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg0);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_314(empty_list, arg0);
Value *rslt5 = protoFnImpl_274(empty_list, rslt4);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt7 = protoFnImpl_220(empty_list, arg0, (Value *)&fn_474);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)(Value *)&fn_377);
varArgs8 = (List *)listCons((Value *)(Value *)&fn_377, varArgs8);
Value *rslt9 = arityImpl_206(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = arityImpl_369(empty_list, rslt9);
decRef(rslt7);
my_free(rslt7);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_220(empty_list, arg0, (Value *)&protoFn_317);
Value *rslt2 = arityImpl_473(closures, rslt1);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
}
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- list=* main body --------------
Function fn_472 = {3, -1, "list=*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_473}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_32 = {1, -1, 1,"("};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_33 = {1, -1, 2,", "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_34 = {1, -1, 1,")"};

// --------- crush_impl --------------
Function fn_477;

// --------- anon --------------
Function fn_479;
Value *arityImpl_480(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((val0)->type != 3) {
rslt4 = protoFnImpl_5(empty_list, val0, arg1);
} else {
FnArity *arity1 = findFnArity(val0, 1);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
rslt4 = fn3(arity1->closures, arg1);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(arg1);
varArgs2 = (List *)listCons(arg1, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val0)->name);
  abort();
}
}
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)arg0);
varArgs5 = (List *)listCons((Value *)arg0, varArgs5);
Value *rslt6 = arityImpl_345(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
decRef(rslt4);
my_free(rslt4);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_478(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_103(empty_list, arg0);
Value *rslt1 = arityImpl_100(empty_list, arg0);
Value *rslt5;
if((arg1)->type != 3) {
rslt5 = protoFnImpl_5(empty_list, arg1, rslt1);
} else {
FnArity *arity2 = findFnArity(arg1, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 2;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_480;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_479 = malloc_function(1);
fn_479->type = 3;
fn_479->name = "anon";
fn_479->arityCount = 1;
fn_479->arities[0] = arity_6;
Value *rslt7 = arityImpl_392(empty_list, rslt0, rslt5, (Value *)fn_479);
incRef(rslt7);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
decRef((Value *)fn_479);
my_free((Value *)fn_479);
decRef(rslt7);
my_free(rslt7);
return(rslt7);
};


// --------- crush_impl main body --------------
Function fn_477 = {3, -1, "crush_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_478}}};


// --------- traverse_impl --------------
Function fn_481;
Value *arityImpl_482(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_220(empty_list, arg0, arg1);
Value *rslt1 = protoFnImpl_314(empty_list, rslt0);
Value *rslt2 = protoFnImpl_193(empty_list, rslt1, (Value *)&fn_211);
Value *rslt3 = protoFnImpl_203(empty_list, rslt2, rslt0);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- traverse_impl main body --------------
Function fn_481 = {3, -1, "traverse_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_482}}};


// --------- =*_impl --------------
Function fn_483;
Value *arityImpl_484(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_61(empty_list, arg0);
Value *rslt5 = arityImpl_61(empty_list, arg1);
Value *rslt6 = arityImpl_378(empty_list, rslt4, rslt5);
Value *rslt7 = arityImpl_369(empty_list, rslt6);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt8 = protoFnImpl_290(empty_list, arg0);
Value *rslt9 = protoFnImpl_290(empty_list, arg1);
Value *rslt10 = arityImpl_74(empty_list, rslt8, rslt9);
Value *rslt11 = arityImpl_369(empty_list, rslt10);
decRef(rslt8);
my_free(rslt8);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt11);
my_free(rslt11);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_473(empty_list, rslt2);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- =*_impl main body --------------
Function fn_483 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_484}}};


// --------- string-list_impl --------------
Function fn_485;
Value *arityImpl_486(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_32);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_32, varArgs0);
Value *rslt1 = arityImpl_212(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_244(empty_list, arg0, (Value *)&_str_33);
Value *rslt3 = protoFnImpl_163(empty_list, rslt2, (Value *)&protoFn_229);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_34);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_34, varArgs4);
Value *rslt5 = arityImpl_212(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_345(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
incRef(rslt7);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
decRef(rslt7);
my_free(rslt7);
return(rslt7);
};


// --------- string-list_impl main body --------------
Function fn_485 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_486}}};


// --------- empty?_impl --------------
Function fn_487;
Value *arityImpl_488(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_97(empty_list, arg0);
Value *rslt1 = arityImpl_74(empty_list, (Value *)&_num_9, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_487 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_488}}};


// --------- empty_impl --------------
Function fn_489;
Value *arityImpl_490(List *closures, Value *arg0) {
incRef(var_91);
return(var_91);
};


// --------- empty_impl main body --------------
Function fn_489 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_490}}};


// --------- conj_impl --------------
Function fn_491;
Value *arityImpl_492(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_94(empty_list, arg1, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- conj_impl main body --------------
Function fn_491 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_492}}};


// --------- count_impl --------------
Function fn_493;
Value *arityImpl_494(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_97(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_493 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_494}}};


// --------- seq?_impl --------------
Function fn_495;
Value *arityImpl_496(List *closures, Value *arg0) {
incRef(var_37);
return(var_37);
};


// --------- seq?_impl main body --------------
Function fn_495 = {3, -1, "seq?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_496}}};


// --------- seq_impl --------------
Function fn_497;
Value *arityImpl_498(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_497 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_498}}};


// --------- first_impl --------------
Function fn_499;
Value *arityImpl_500(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_100(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- first_impl main body --------------
Function fn_499 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_500}}};


// --------- rest_impl --------------
Function fn_501;
Value *arityImpl_502(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_103(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_501 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_502}}};


// --------- zero_impl --------------
Function fn_503;
Value *arityImpl_504(List *closures, Value *arg0) {
incRef(var_91);
return(var_91);
};


// --------- zero_impl main body --------------
Function fn_503 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_504}}};


// --------- comp*_impl --------------
Function fn_505;
Value *arityImpl_506(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_94(empty_list, arg0, arg1);
Value *rslt1 = arityImpl_470(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_505 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_506}}};


// --------- map_impl --------------
Function fn_507;
Value *arityImpl_508(List *closures, Value *arg0, Value *arg1) {
List *l = (List *)arg0;
      if (l->len == 0)
        return((Value *)empty_list);
      else {
        List *head = empty_list;
        List *tail;
        for(Value *x = l->head; x != (Value *)0; l = l->tail, x = l->head) {
          Value *y;
          if(arg1->type != 3) {
            y = protoFnImpl_5(empty_list, arg1, x);
          } else {
            FnArity *arity2 = findFnArity(arg1, 1);
            if(arity2 != (FnArity *)0 && !arity2->variadic) {
              FnType1 *fn4 = (FnType1 *)arity2->fn;
              y = fn4(arity2->closures, x);
            } else if(arity2 != (FnArity *)0 && arity2->variadic) {
              FnType1 *fn4 = (FnType1 *)arity2->fn;
              incRef(x);
              List *varArgs3 = (List *)listCons(x, empty_list);
              y = fn4(arity2->closures, (Value *)varArgs3);
              decRef((Value *)varArgs3);
              my_free((Value *)varArgs3);
            } else {
              fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
              abort();
            }
          }

          // 'y' is the value for the new list

          if (head == empty_list) {
            // if we haven't started the new list yet
            head = malloc_list();
            head->type = ListType;
            head->len = 1;
            head->head = y;
            head->tail = empty_list;
            tail = head;
          } else {
            // otherwise, append to tail of list
            List *new_tail = malloc_list();
            new_tail->type = ListType;
            new_tail->len = 1;
            new_tail->head = y;
            new_tail->tail = empty_list;
            tail->tail = new_tail;
            tail = new_tail;
            head->len++;
          }
        }
        return((Value *)head);
      }
};


// --------- map_impl main body --------------
Function fn_507 = {3, -1, "map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_508}}};


// --------- wrap_impl --------------
Function fn_509;
Value *arityImpl_510(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
Value *rslt1 = arityImpl_212(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- wrap_impl main body --------------
Function fn_509 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_510}}};


// --------- flat-map_impl --------------
Function fn_511;
Value *arityImpl_512(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_220(empty_list, arg0, arg1);
Value *cond1;
Value *rslt5 = protoFnImpl_274(empty_list, rslt0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_91);
cond1 = var_91;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt2 = arityImpl_100(empty_list, rslt0);
Value *rslt3 = arityImpl_103(empty_list, rslt0);
Value *rslt4 = protoFnImpl_342(empty_list, rslt2, rslt3);
incRef(rslt4);
cond1 = rslt4;
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond1);
decRef(rslt0);
my_free(rslt0);
decRef(cond1);
my_free(cond1);
return(cond1);
};


// --------- flat-map_impl main body --------------
Function fn_511 = {3, -1, "flat-map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_512}}};


// --------- some --------------
Function fn_513;
Value *arityImpl_514(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg0);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_314(empty_list, arg0);
Value *rslt8;
if((arg1)->type != 3) {
rslt8 = protoFnImpl_5(empty_list, arg1, rslt4);
} else {
FnArity *arity5 = findFnArity(arg1, 1);
if(arity5 != (FnArity *)0 && !arity5->variadic) {
FnType1 *fn7 = (FnType1 *)arity5->fn;
rslt8 = fn7(arity5->closures, rslt4);
} else if(arity5 != (FnArity *)0 && arity5->variadic) {
FnType1 *fn7 = (FnType1 *)arity5->fn;
List *varArgs6 = empty_list;
incRef(rslt4);
varArgs6 = (List *)listCons(rslt4, varArgs6);
rslt8 = fn7(arity5->closures, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
decRef(rslt4);
my_free(rslt4);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt1 = protoFnImpl_319(empty_list, arg0);
Value *rslt2 = arityImpl_514(closures, rslt1, arg1);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- some main body --------------
Function fn_513 = {3, -1, "some", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_514}}};


// --------- inc --------------
Function fn_516;
Value *arityImpl_517(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_80(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- inc main body --------------
Function fn_516 = {3, -1, "inc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_517}}};


// --------- + --------------
Function fn_519;
Value *arityImpl_520(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_274(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_392(empty_list, arg0, (Value *)&_num_9, (Value *)&fn_79);
incRef(rslt1);
cond0 = rslt1;
decRef(rslt1);
my_free(rslt1);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- + main body --------------
Function fn_519 = {3, -1, "+", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_520}}};


// --------- * --------------
Function fn_522;
Value *arityImpl_523(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_274(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_392(empty_list, arg0, (Value *)&_num_1, (Value *)&fn_85);
incRef(rslt1);
cond0 = rslt1;
decRef(rslt1);
my_free(rslt1);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- * main body --------------
Function fn_522 = {3, -1, "*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_523}}};


// --------- dec --------------
Function fn_525;
Value *arityImpl_526(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_83(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- dec main body --------------
Function fn_525 = {3, -1, "dec", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_526}}};


// --------- - --------------
Function fn_528;
Value *arityImpl_529(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt6 = protoFnImpl_274(empty_list, arg0);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_314(empty_list, arg0);
Value *rslt2 = protoFnImpl_319(empty_list, arg0);
Value *cond3;
Value *rslt5 = protoFnImpl_274(empty_list, rslt2);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(rslt1);
cond3 = rslt1;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt4 = arityImpl_392(empty_list, rslt2, rslt1, (Value *)&fn_82);
incRef(rslt4);
cond3 = rslt4;
decRef(rslt4);
my_free(rslt4);
}
incRef(cond3);
cond0 = cond3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(cond3);
my_free(cond3);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- - main body --------------
Function fn_528 = {3, -1, "-", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_529}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_35 = {1, -1, 0,""};

// --------- =*_impl --------------
Function fn_531;
Value *arityImpl_532(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_115(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_531 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_532}}};


// --------- empty?_impl --------------
Function fn_533;
Value *arityImpl_534(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_112(empty_list, arg0);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_9, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_533 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_534}}};


// --------- empty_impl --------------
Function fn_535;
Value *arityImpl_536(List *closures, Value *arg0) {
incRef((Value *)&_str_35);
return((Value *)&_str_35);
};


// --------- empty_impl main body --------------
Function fn_535 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_536}}};


// --------- count_impl --------------
Function fn_537;
Value *arityImpl_538(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_112(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_537 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_538}}};


// --------- conj_impl --------------
Function fn_539;
Value *arityImpl_540(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_212(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_163(empty_list, rslt1, (Value *)&protoFn_229);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_344);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_344, varArgs3);
Value *rslt4 = arityImpl_206(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
incRef(rslt4);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};


// --------- conj_impl main body --------------
Function fn_539 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_540}}};


// --------- seq_impl --------------
Function fn_541;
Value *arityImpl_542(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_378(empty_list, arg0, (Value *)&_str_35);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_68(empty_list, arg0, (Value *)&_num_9, (Value *)&_num_1);
Value *rslt2 = arityImpl_67(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_309(empty_list, rslt2);
Value *rslt4 = arityImpl_94(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- seq_impl main body --------------
Function fn_541 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_542}}};


// --------- first_impl --------------
Function fn_543;
Value *arityImpl_544(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = arityImpl_378(empty_list, arg0, (Value *)&_str_35);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = arityImpl_58(empty_list);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt3);
my_free(rslt3);
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_68(empty_list, arg0, (Value *)&_num_9, (Value *)&_num_1);
incRef(rslt1);
cond0 = rslt1;
decRef(rslt1);
my_free(rslt1);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- first_impl main body --------------
Function fn_543 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_544}}};


// --------- rest_impl --------------
Function fn_545;
Value *arityImpl_546(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_67(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_545 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_546}}};


// --------- string-list_impl --------------
Function fn_547;
Value *arityImpl_548(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_212(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_547 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_548}}};


// --------- comp*_impl --------------
Function fn_549;

// --------- anon --------------
Function fn_551;
Value *arityImpl_552(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_112(empty_list, arg1);
Value *rslt1 = arityImpl_80(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_551 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_552}}};


// --------- anon --------------
Function fn_553;
Value *arityImpl_554(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_124(empty_list, val0, arg0);
incRef((Value *)&_num_9);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_9);
};

Value *arityImpl_550(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_241(empty_list, arg1);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt1 = arityImpl_94(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_163(empty_list, rslt1, (Value *)&protoFn_229);
Value *rslt4 = arityImpl_392(empty_list, rslt2, (Value *)&_num_9, (Value *)&fn_551);
Value *rslt5 = arityImpl_121(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_554;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_553 = malloc_function(1);
fn_553->type = 3;
fn_553->name = "anon";
fn_553->arityCount = 1;
fn_553->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_220(empty_list, rslt2, (Value *)fn_553);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef((Value *)fn_553);
my_free((Value *)fn_553);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_549 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_550}}};


// --------- string-list_impl --------------
Function fn_555;
Value *arityImpl_556(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_212(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_555 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_556}}};


// --------- =*_impl --------------
Function fn_557;
Value *arityImpl_558(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_115(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_557 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_558}}};


// --------- empty?_impl --------------
Function fn_559;
Value *arityImpl_560(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_112(empty_list, arg0);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_9, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_559 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_560}}};


// --------- empty_impl --------------
Function fn_561;
Value *arityImpl_562(List *closures, Value *arg0) {
incRef((Value *)&_str_35);
return((Value *)&_str_35);
};


// --------- empty_impl main body --------------
Function fn_561 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_562}}};


// --------- count_impl --------------
Function fn_563;
Value *arityImpl_564(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_112(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_563 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_564}}};


// --------- conj_impl --------------
Function fn_565;
Value *arityImpl_566(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_212(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_163(empty_list, rslt1, (Value *)&protoFn_229);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_344);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_344, varArgs3);
Value *rslt4 = arityImpl_206(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
incRef(rslt4);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};


// --------- conj_impl main body --------------
Function fn_565 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_566}}};


// --------- seq_impl --------------
Function fn_567;
Value *arityImpl_568(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_378(empty_list, arg0, (Value *)&_str_35);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_68(empty_list, arg0, (Value *)&_num_9, (Value *)&_num_1);
Value *rslt2 = arityImpl_67(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_309(empty_list, rslt2);
Value *rslt4 = arityImpl_94(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- seq_impl main body --------------
Function fn_567 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_568}}};


// --------- first_impl --------------
Function fn_569;
Value *arityImpl_570(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = arityImpl_378(empty_list, arg0, (Value *)&_str_35);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = arityImpl_58(empty_list);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt3);
my_free(rslt3);
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_68(empty_list, arg0, (Value *)&_num_9, (Value *)&_num_1);
incRef(rslt1);
cond0 = rslt1;
decRef(rslt1);
my_free(rslt1);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- first_impl main body --------------
Function fn_569 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_570}}};


// --------- rest_impl --------------
Function fn_571;
Value *arityImpl_572(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_67(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_571 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_572}}};


// --------- comp*_impl --------------
Function fn_573;

// --------- anon --------------
Function fn_575;
Value *arityImpl_576(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_112(empty_list, arg1);
Value *rslt1 = arityImpl_80(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_575 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_576}}};


// --------- anon --------------
Function fn_577;
Value *arityImpl_578(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_124(empty_list, val0, arg0);
incRef((Value *)&_num_9);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_9);
};

Value *arityImpl_574(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_241(empty_list, arg1);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt1 = arityImpl_94(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_163(empty_list, rslt1, (Value *)&protoFn_229);
Value *rslt4 = arityImpl_392(empty_list, rslt2, (Value *)&_num_9, (Value *)&fn_575);
Value *rslt5 = arityImpl_121(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_578;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_577 = malloc_function(1);
fn_577->type = 3;
fn_577->name = "anon";
fn_577->arityCount = 1;
fn_577->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_220(empty_list, rslt2, (Value *)fn_577);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef((Value *)fn_577);
my_free((Value *)fn_577);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_573 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_574}}};


// --------- str --------------
Function fn_579;

// --------- anon --------------
Function fn_581;
Value *arityImpl_582(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_112(empty_list, arg1);
Value *rslt1 = arityImpl_80(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_581 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_582}}};


// --------- anon --------------
Function fn_583;
Value *arityImpl_584(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_124(empty_list, val0, arg0);
incRef((Value *)&_num_9);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_9);
};

Value *arityImpl_580(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt7 = protoFnImpl_274(empty_list, arg0);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef((Value *)&_str_35);
cond0 = (Value *)&_str_35;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_163(empty_list, arg0, (Value *)&protoFn_229);
Value *rslt3 = arityImpl_392(empty_list, rslt1, (Value *)&_num_9, (Value *)&fn_581);
Value *rslt4 = arityImpl_121(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_584;
incRef((Value *)rslt4);
arity_5->closures = listCons((Value *)rslt4, (List *)arity_5->closures);
Function *fn_583 = malloc_function(1);
fn_583->type = 3;
fn_583->name = "anon";
fn_583->arityCount = 1;
fn_583->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_220(empty_list, rslt1, (Value *)fn_583);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef((Value *)fn_583);
my_free((Value *)fn_583);
decRef(rslt6);
my_free(rslt6);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- str main body --------------
Function fn_579 = {3, -1, "str", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_580}}};


// --------- take --------------
Function fn_586;
Value *arityImpl_587(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = protoFnImpl_274(empty_list, arg0);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = arityImpl_378(empty_list, (Value *)&_num_9, arg1);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_314(empty_list, arg0);
Value *rslt2 = protoFnImpl_319(empty_list, arg0);
Value *rslt3 = arityImpl_526(empty_list, arg1);
Value *rslt4 = arityImpl_587(closures, rslt2, rslt3);
Value *rslt5 = arityImpl_94(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- take main body --------------
Function fn_586 = {3, -1, "take", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_587}}};


// --------- drop --------------
Function fn_589;
Value *arityImpl_590(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_382(empty_list, arg1, (Value *)&_num_1);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = protoFnImpl_319(empty_list, arg0);
Value *rslt2 = arityImpl_526(empty_list, arg1);
Value *rslt3 = arityImpl_590(closures, rslt1, rslt2);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- drop main body --------------
Function fn_589 = {3, -1, "drop", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_590}}};


// --------- split --------------
Function fn_592;
Value *arityImpl_593(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt6 = protoFnImpl_274(empty_list, arg0);
Value *rslt7 = arityImpl_382(empty_list, arg1, (Value *)&_num_1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_375(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = arityImpl_403(empty_list, arg2);
List *varArgs11 = empty_list;
incRef((Value *)arg0);
varArgs11 = (List *)listCons((Value *)arg0, varArgs11);
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
Value *rslt12 = arityImpl_212(empty_list, (Value *)varArgs11);
decRef((Value *)varArgs11);
my_free((Value *)varArgs11);
incRef(rslt12);
cond0 = rslt12;
decRef(rslt10);
my_free(rslt10);
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt1 = protoFnImpl_319(empty_list, arg0);
Value *rslt2 = arityImpl_526(empty_list, arg1);
Value *rslt3 = protoFnImpl_314(empty_list, arg0);
Value *rslt4 = arityImpl_94(empty_list, rslt3, arg2);
Value *rslt5 = arityImpl_593(closures, rslt1, rslt2, rslt4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *arityImpl_594(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if(((Value *)&fn_592)->type != 3) {
rslt3 = protoFnImpl_9(empty_list, (Value *)&fn_592, arg0, arg1, var_91);
} else {
FnArity *arity0 = findFnArity((Value *)&fn_592, 3);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType3 *fn2 = (FnType3 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg0, arg1, var_91);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_91);
varArgs1 = (List *)listCons(var_91, varArgs1);
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_592)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- split main body --------------
Function fn_592 = {3, -1, "split", 2, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_593}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_594}}};


// --------- replace-at-nth --------------
Function fn_596;
Value *arityImpl_597(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt9 = protoFnImpl_274(empty_list, arg0);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_290(empty_list, arg0);
Value *rslt11 = arityImpl_526(empty_list, rslt10);
Value *rslt12 = arityImpl_382(empty_list, rslt11, arg1);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt12);
my_free(rslt12);
Value *rslt1 = arityImpl_594(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_314(empty_list, rslt1);
List *varArgs3 = empty_list;
incRef((Value *)arg2);
varArgs3 = (List *)listCons((Value *)arg2, varArgs3);
Value *rslt4 = arityImpl_212(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_322(empty_list, rslt1);
Value *rslt6 = protoFnImpl_319(empty_list, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
incRef((Value *)rslt2);
varArgs7 = (List *)listCons((Value *)rslt2, varArgs7);
Value *rslt8 = arityImpl_345(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
decRef(rslt8);
my_free(rslt8);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- replace-at-nth main body --------------
Function fn_596 = {3, -1, "replace-at-nth", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_597}}};


// --------- remove-nth --------------
Function fn_599;
Value *arityImpl_600(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt7 = protoFnImpl_274(empty_list, arg0);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt8 = protoFnImpl_290(empty_list, arg0);
Value *rslt9 = arityImpl_526(empty_list, rslt8);
Value *rslt10 = arityImpl_382(empty_list, rslt9, arg1);
decRef(rslt8);
my_free(rslt8);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = arityImpl_594(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_314(empty_list, rslt1);
Value *rslt3 = arityImpl_322(empty_list, rslt1);
Value *rslt4 = protoFnImpl_319(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
Value *rslt6 = arityImpl_345(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef(rslt6);
my_free(rslt6);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- remove-nth main body --------------
Function fn_599 = {3, -1, "remove-nth", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_600}}};


// --------- partition --------------
Function fn_602;
Value *arityImpl_603(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_290(empty_list, arg0);
Value *rslt6 = arityImpl_382(empty_list, rslt5, arg1);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_587(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_590(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_603(closures, rslt2, arg1);
Value *rslt4 = arityImpl_94(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- partition main body --------------
Function fn_602 = {3, -1, "partition", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_603}}};


// --------- partition-all --------------
Function fn_605;
Value *arityImpl_606(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_290(empty_list, arg0);
Value *rslt6 = arityImpl_382(empty_list, rslt5, arg1);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
List *varArgs7 = empty_list;
incRef((Value *)arg0);
varArgs7 = (List *)listCons((Value *)arg0, varArgs7);
Value *rslt8 = arityImpl_212(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_587(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_590(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_606(closures, rslt2, arg1);
Value *rslt4 = arityImpl_94(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- partition-all main body --------------
Function fn_605 = {3, -1, "partition-all", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_606}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_36 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_608;
Value *arityImpl_609(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_274(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_str_36);
varArgs6 = (List *)listCons((Value *)(Value *)&_str_36, varArgs6);
Value *rslt7 = arityImpl_258(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
Value *rslt8 = arityImpl_58(empty_list);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt9 = arityImpl_378(empty_list, arg1, (Value *)&_num_9);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_309(empty_list, arg0);
Value *rslt11 = protoFnImpl_314(empty_list, rslt10);
incRef(rslt11);
cond0 = rslt11;
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt1 = protoFnImpl_309(empty_list, arg0);
Value *rslt2 = protoFnImpl_319(empty_list, rslt1);
Value *rslt3 = arityImpl_526(empty_list, arg1);
Value *rslt4 = arityImpl_609(closures, rslt2, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *arityImpl_610(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = protoFnImpl_274(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(arg2);
cond0 = arg2;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt6 = arityImpl_378(empty_list, arg1, (Value *)&_num_9);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_309(empty_list, arg0);
Value *rslt8 = protoFnImpl_314(empty_list, rslt7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_309(empty_list, arg0);
Value *rslt2 = protoFnImpl_319(empty_list, rslt1);
Value *rslt3 = arityImpl_526(empty_list, arg1);
Value *rslt4 = arityImpl_610(closures, rslt2, rslt3, arg2);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- nth main body --------------
Function fn_608 = {3, -1, "nth", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_609}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_610}}};


// --------- last --------------
Function fn_612;
Value *arityImpl_613(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_290(empty_list, arg0);
Value *rslt1 = arityImpl_526(empty_list, rslt0);
Value *rslt2 = arityImpl_609(empty_list, arg0, rslt1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- last main body --------------
Function fn_612 = {3, -1, "last", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_613}}};


// --------- butlast --------------
Function fn_615;
Value *arityImpl_616(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = protoFnImpl_274(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt6 = protoFnImpl_290(empty_list, arg0);
Value *rslt7 = arityImpl_378(empty_list, (Value *)&_num_1, rslt6);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_314(empty_list, arg0);
Value *rslt2 = protoFnImpl_319(empty_list, arg0);
Value *rslt3 = arityImpl_616(closures, rslt2);
Value *rslt4 = arityImpl_94(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- butlast main body --------------
Function fn_615 = {3, -1, "butlast", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_616}}};


// --------- map-assoc --------------
Function fn_618;
Value *arityImpl_619(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = arityImpl_241(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)arg2);
varArgs6 = (List *)listCons((Value *)arg2, varArgs6);
incRef((Value *)arg1);
varArgs6 = (List *)listCons((Value *)arg1, varArgs6);
Value *rslt7 = arityImpl_212(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
Value *rslt9 = arityImpl_212(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
incRef(rslt9);
cond0 = rslt9;
decRef(rslt7);
my_free(rslt7);
decRef(rslt9);
my_free(rslt9);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt10 = arityImpl_100(empty_list, arg0);
Value *rslt11 = arityImpl_100(empty_list, rslt10);
Value *rslt12 = arityImpl_378(empty_list, rslt11, arg1);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
List *varArgs13 = empty_list;
incRef((Value *)arg2);
varArgs13 = (List *)listCons((Value *)arg2, varArgs13);
incRef((Value *)arg1);
varArgs13 = (List *)listCons((Value *)arg1, varArgs13);
Value *rslt14 = arityImpl_212(empty_list, (Value *)varArgs13);
decRef((Value *)varArgs13);
my_free((Value *)varArgs13);
Value *rslt15 = arityImpl_103(empty_list, arg0);
Value *rslt16 = arityImpl_94(empty_list, rslt14, rslt15);
incRef(rslt16);
cond0 = rslt16;
decRef(rslt14);
my_free(rslt14);
decRef(rslt15);
my_free(rslt15);
decRef(rslt16);
my_free(rslt16);
} else {
decRef(rslt12);
my_free(rslt12);
Value *rslt1 = arityImpl_100(empty_list, arg0);
Value *rslt2 = arityImpl_103(empty_list, arg0);
Value *rslt3 = arityImpl_619(closures, rslt2, arg1, arg2);
Value *rslt4 = arityImpl_94(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- map-assoc main body --------------
Function fn_618 = {3, -1, "map-assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_619}}};


// --------- map-get --------------
Function fn_621;
Value *arityImpl_622(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt3 = arityImpl_241(empty_list, arg0);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef(arg2);
cond0 = arg2;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = arityImpl_100(empty_list, arg0);
Value *rslt5 = arityImpl_100(empty_list, rslt4);
Value *rslt6 = arityImpl_378(empty_list, rslt5, arg1);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = arityImpl_100(empty_list, arg0);
Value *rslt8 = arityImpl_103(empty_list, rslt7);
Value *rslt9 = arityImpl_100(empty_list, rslt8);
incRef(rslt9);
cond0 = rslt9;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
decRef(rslt9);
my_free(rslt9);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_103(empty_list, arg0);
Value *rslt2 = arityImpl_622(closures, rslt1, arg1, arg2);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- map-get main body --------------
Function fn_621 = {3, -1, "map-get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_622}}};

SubString _kw_3 = {5, -1, 6, 0, ":hm-nf"};

// --------- hash-map= --------------
Function fn_624;
Value *arityImpl_625(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt13 = protoFnImpl_274(empty_list, arg0);
decRef(rslt13);
my_free(rslt13);

if (isTrue(rslt13)) {
decRef(rslt13);
my_free(rslt13);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
decRef(rslt13);
my_free(rslt13);
Value *rslt1 = protoFnImpl_314(empty_list, arg0);
Value *rslt2 = protoFnImpl_314(empty_list, rslt1);
Value *rslt3 = protoFnImpl_319(empty_list, rslt1);
Value *rslt4 = protoFnImpl_314(empty_list, rslt3);
Value *cond5;
Value *rslt8 = arityImpl_378(empty_list, (Value *)&_kw_3, rslt2);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_9);
cond5 = (Value *)&_num_9;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt9 = arityImpl_378(empty_list, (Value *)&_kw_3, rslt4);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef((Value *)&_num_9);
cond5 = (Value *)&_num_9;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_356(empty_list, arg1, rslt2, (Value *)&_kw_3);
Value *rslt11 = arityImpl_378(empty_list, rslt4, rslt10);
Value *rslt12 = arityImpl_369(empty_list, rslt11);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
incRef((Value *)&_num_9);
cond5 = (Value *)&_num_9;
} else {
decRef(rslt12);
my_free(rslt12);
Value *rslt6 = protoFnImpl_319(empty_list, arg0);
Value *rslt7 = arityImpl_625(closures, rslt6, arg1);
incRef(rslt7);
cond5 = rslt7;
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);
}
}
}
incRef(cond5);
cond0 = cond5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef(cond5);
my_free(cond5);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- hash-map= main body --------------
Function fn_624 = {3, -1, "hash-map=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_625}}};

ProtoImpls *protoImpls_627;
Value *protoFnImpl_630(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_627);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '.a-list' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to '.a-list'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_631 = {8, -1, 1, (List *)0, 0, protoFnImpl_630};
Function protoFn_628 = {3, -1, ".a-list", 1, {&protoFnArity_631}};

// forward declaration for 'HashMap'
Value *var_632;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_37 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_38 = {1, -1, 1,"{"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_39 = {1, -1, 1,"}"};
Number _num_11 = {2, -1, 12};

// --------- instance?_impl --------------
Function fn_633;
Value *arityImpl_634(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_61(empty_list, arg1);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_11, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_633 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_634}}};

Value *protoImpl_635(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_636 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_635}}};


// --------- invoke_impl --------------
Function fn_637;

// --------- seq_impl --------------
Function fn_639;
Value *arityImpl_640(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_641(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_642 = {3, -1, "seq", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_641}}};


// --------- first_impl --------------
Function fn_643;
Value *arityImpl_644(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_100(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_645(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_646 = {3, -1, "first", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_645}}};


// --------- rest_impl --------------
Function fn_647;
Value *arityImpl_648(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_103(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_649(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_650 = {3, -1, "rest", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_649}}};


// --------- =*_impl --------------
Function fn_651;
Value *arityImpl_652(List *closures, Value *arg0, Value *arg1) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt3 = protoFnImpl_290(empty_list, val1);
Value *rslt4 = protoFnImpl_309(empty_list, arg1);
Value *rslt5 = protoFnImpl_290(empty_list, rslt4);
Value *rslt6 = arityImpl_378(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_369(empty_list, rslt6);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef((Value *)&_num_9);
cond0 = (Value *)&_num_9;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt2 = arityImpl_625(empty_list, val1, arg1);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoImpl_653(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_654 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_653}}};


// --------- string-list_impl --------------
Function fn_655;

// --------- anon --------------
Function fn_657;
Value *arityImpl_658(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_220(empty_list, arg0, (Value *)&protoFn_229);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_23);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_23, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_244(empty_list, rslt0, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_344);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_344, varArgs4);
Value *rslt5 = arityImpl_206(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};


// --------- anon main body --------------
Function fn_657 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_658}}};

Value *arityImpl_656(List *closures, Value *arg0) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt15 = arityImpl_241(empty_list, val1);
decRef(rslt15);
my_free(rslt15);

if (isTrue(rslt15)) {
decRef(rslt15);
my_free(rslt15);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_37);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_37, varArgs16);
Value *rslt17 = arityImpl_212(empty_list, (Value *)varArgs16);
decRef((Value *)varArgs16);
my_free((Value *)varArgs16);
incRef(rslt17);
cond0 = rslt17;
decRef(rslt17);
my_free(rslt17);
} else {
decRef(rslt15);
my_free(rslt15);
Value *rslt3 = protoFnImpl_220(empty_list, val1, (Value *)&fn_657);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_33);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_33, varArgs4);
Value *rslt5 = arityImpl_212(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = arityImpl_244(empty_list, rslt3, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)(Value *)&fn_344);
varArgs7 = (List *)listCons((Value *)(Value *)&fn_344, varArgs7);
Value *rslt8 = arityImpl_206(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&_str_38);
varArgs9 = (List *)listCons((Value *)(Value *)&_str_38, varArgs9);
Value *rslt10 = arityImpl_212(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_39);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_39, varArgs11);
Value *rslt12 = arityImpl_212(empty_list, (Value *)varArgs11);
decRef((Value *)varArgs11);
my_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)rslt12);
varArgs13 = (List *)listCons((Value *)rslt12, varArgs13);
incRef((Value *)rslt8);
varArgs13 = (List *)listCons((Value *)rslt8, varArgs13);
incRef((Value *)rslt10);
varArgs13 = (List *)listCons((Value *)rslt10, varArgs13);
Value *rslt14 = arityImpl_345(empty_list, (Value *)varArgs13);
decRef((Value *)varArgs13);
my_free((Value *)varArgs13);
incRef(rslt14);
cond0 = rslt14;
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
decRef(rslt8);
my_free(rslt8);
decRef(rslt10);
my_free(rslt10);
decRef(rslt12);
my_free(rslt12);
decRef(rslt14);
my_free(rslt14);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoImpl_659(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_660 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_659}}};


// --------- empty?_impl --------------
Function fn_661;
Value *arityImpl_662(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_274(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_663(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_664 = {3, -1, "empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_663}}};


// --------- count_impl --------------
Function fn_665;
Value *arityImpl_666(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_290(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_667(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_668 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_667}}};


// --------- zero_impl --------------
Function fn_669;
Value *arityImpl_670(List *closures, Value *arg0) {
Value *rslt3;
if((var_632)->type != 3) {
rslt3 = protoFnImpl_5(empty_list, var_632, var_91);
} else {
FnArity *arity0 = findFnArity(var_632, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, var_91);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_91);
varArgs1 = (List *)listCons(var_91, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_632)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- zero_impl main body --------------
Function fn_669 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_670}}};

Value *protoImpl_671(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_672 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_671}}};


// --------- comp*_impl --------------
Function fn_673;

// --------- anon --------------
Function fn_675;

// --------- anon --------------
Function fn_677;
Value *arityImpl_678(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_609(empty_list, arg1, (Value *)&_num_9);
Value *rslt1 = arityImpl_609(empty_list, arg1, (Value *)&_num_1);
Value *rslt2 = protoFnImpl_350(empty_list, arg0, rslt0, rslt1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_677 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_678}}};

Value *arityImpl_676(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_309(empty_list, arg1);
Value *rslt2 = arityImpl_392(empty_list, rslt0, arg0, (Value *)&fn_677);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_675 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_676}}};

Value *arityImpl_674(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg1);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt2 = arityImpl_392(empty_list, arg1, arg0, (Value *)&fn_675);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_673 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_674}}};

Value *protoImpl_679(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_680 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_679}}};


// --------- assoc_impl --------------
Function fn_681;
Value *arityImpl_682(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_619(empty_list, val0, arg1, arg2);
Value *rslt5;
if((var_632)->type != 3) {
rslt5 = protoFnImpl_5(empty_list, var_632, rslt1);
} else {
FnArity *arity2 = findFnArity(var_632, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_632)->name);
  abort();
}
}
incRef(rslt5);
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoImpl_683(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_684 = {3, -1, "assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_683}}};


// --------- get_impl --------------
Function fn_685;
Value *arityImpl_686(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_622(empty_list, val0, arg1, arg2);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_687(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_688 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_687}}};


// --------- keys_impl --------------
Function fn_689;
Value *arityImpl_690(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_220(empty_list, val0, (Value *)&protoFn_312);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_691(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[11])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_692 = {3, -1, "keys", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_691}}};


// --------- vals_impl --------------
Function fn_693;
Value *arityImpl_694(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_220(empty_list, val0, (Value *)&fn_321);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_695(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[12])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_696 = {3, -1, "vals", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_695}}};


// --------- .a-list_impl --------------
Function fn_697;
Value *arityImpl_698(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_699(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[13])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_700 = {3, -1, ".a-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_699}}};

Value *arityImpl_638(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_640;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_639 = malloc_function(1);
fn_639->type = 3;
fn_639->name = "seq_impl";
fn_639->arityCount = 1;
fn_639->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_644;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_643 = malloc_function(1);
fn_643->type = 3;
fn_643->name = "first_impl";
fn_643->arityCount = 1;
fn_643->arities[0] = arity_1;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = 8;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_648;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_647 = malloc_function(1);
fn_647->type = 3;
fn_647->name = "rest_impl";
fn_647->arityCount = 1;
fn_647->arities[0] = arity_2;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_652;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_651 = malloc_function(1);
fn_651->type = 3;
fn_651->name = "=*_impl";
fn_651->arityCount = 1;
fn_651->arities[0] = arity_3;
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 1;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_656;
incRef((Value *)arg1);
arity_4->closures = listCons((Value *)arg1, (List *)arity_4->closures);
Function *fn_655 = malloc_function(1);
fn_655->type = 3;
fn_655->name = "string-list_impl";
fn_655->arityCount = 1;
fn_655->arities[0] = arity_4;
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_662;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_661 = malloc_function(1);
fn_661->type = 3;
fn_661->name = "empty?_impl";
fn_661->arityCount = 1;
fn_661->arities[0] = arity_5;
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_666;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_665 = malloc_function(1);
fn_665->type = 3;
fn_665->name = "count_impl";
fn_665->arityCount = 1;
fn_665->arities[0] = arity_6;
FnArity *arity_9 = malloc_fnArity();
arity_9->type = 8;
arity_9->count = 3;
arity_9->closures = empty_list;
arity_9->variadic = 0;
arity_9->fn = arityImpl_682;
incRef((Value *)arg1);
arity_9->closures = listCons((Value *)arg1, (List *)arity_9->closures);
Function *fn_681 = malloc_function(1);
fn_681->type = 3;
fn_681->name = "assoc_impl";
fn_681->arityCount = 1;
fn_681->arities[0] = arity_9;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = 8;
arity_10->count = 3;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_686;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_685 = malloc_function(1);
fn_685->type = 3;
fn_685->name = "get_impl";
fn_685->arityCount = 1;
fn_685->arities[0] = arity_10;
FnArity *arity_11 = malloc_fnArity();
arity_11->type = 8;
arity_11->count = 1;
arity_11->closures = empty_list;
arity_11->variadic = 0;
arity_11->fn = arityImpl_690;
incRef((Value *)arg1);
arity_11->closures = listCons((Value *)arg1, (List *)arity_11->closures);
Function *fn_689 = malloc_function(1);
fn_689->type = 3;
fn_689->name = "keys_impl";
fn_689->arityCount = 1;
fn_689->arities[0] = arity_11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = 8;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_694;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_693 = malloc_function(1);
fn_693->type = 3;
fn_693->name = "vals_impl";
fn_693->arityCount = 1;
fn_693->arities[0] = arity_12;
FnArity *arity_13 = malloc_fnArity();
arity_13->type = 8;
arity_13->count = 1;
arity_13->closures = empty_list;
arity_13->variadic = 0;
arity_13->fn = arityImpl_698;
incRef((Value *)arg1);
arity_13->closures = listCons((Value *)arg1, (List *)arity_13->closures);
Function *fn_697 = malloc_function(1);
fn_697->type = 3;
fn_697->name = ".a-list_impl";
fn_697->arityCount = 1;
fn_697->arities[0] = arity_13;
Value *reified_14 = (Value *)malloc_reified(14);
((ReifiedVal *)reified_14)->type = 12;
((ReifiedVal *)reified_14)->implCount = 14;
((ReifiedVal *)reified_14)->impls[0] = (Value *)fn_639;
incRef((Value *)fn_639);
((ReifiedVal *)reified_14)->impls[1] = (Value *)fn_643;
incRef((Value *)fn_643);
((ReifiedVal *)reified_14)->impls[2] = (Value *)fn_647;
incRef((Value *)fn_647);
((ReifiedVal *)reified_14)->impls[3] = (Value *)fn_651;
incRef((Value *)fn_651);
((ReifiedVal *)reified_14)->impls[4] = (Value *)fn_655;
incRef((Value *)fn_655);
((ReifiedVal *)reified_14)->impls[5] = (Value *)fn_661;
incRef((Value *)fn_661);
((ReifiedVal *)reified_14)->impls[6] = (Value *)fn_665;
incRef((Value *)fn_665);
((ReifiedVal *)reified_14)->impls[7] = (Value *)&fn_669;
incRef((Value *)&fn_669);
((ReifiedVal *)reified_14)->impls[8] = (Value *)&fn_673;
incRef((Value *)&fn_673);
((ReifiedVal *)reified_14)->impls[9] = (Value *)fn_681;
incRef((Value *)fn_681);
((ReifiedVal *)reified_14)->impls[10] = (Value *)fn_685;
incRef((Value *)fn_685);
((ReifiedVal *)reified_14)->impls[11] = (Value *)fn_689;
incRef((Value *)fn_689);
((ReifiedVal *)reified_14)->impls[12] = (Value *)fn_693;
incRef((Value *)fn_693);
((ReifiedVal *)reified_14)->impls[13] = (Value *)fn_697;
incRef((Value *)fn_697);
incRef(reified_14);
decRef((Value *)fn_639);
my_free((Value *)fn_639);
decRef((Value *)fn_643);
my_free((Value *)fn_643);
decRef((Value *)fn_647);
my_free((Value *)fn_647);
decRef((Value *)fn_651);
my_free((Value *)fn_651);
decRef((Value *)fn_655);
my_free((Value *)fn_655);
decRef((Value *)fn_661);
my_free((Value *)fn_661);
decRef((Value *)fn_665);
my_free((Value *)fn_665);
decRef((Value *)fn_681);
my_free((Value *)fn_681);
decRef((Value *)fn_685);
my_free((Value *)fn_685);
decRef((Value *)fn_689);
my_free((Value *)fn_689);
decRef((Value *)fn_693);
my_free((Value *)fn_693);
decRef((Value *)fn_697);
my_free((Value *)fn_697);
decRef(reified_14);
my_free(reified_14);
return(reified_14);
};


// --------- invoke_impl main body --------------
Function fn_637 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_638}}};

Value *protoImpl_701(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_702 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_701}}};

ReifiedVal reified_703 = {11, -1, 2, {(Value *)&fn_633, (Value *)&fn_637}};
Value *var_632 = (Value *)&reified_703;

// --------- hash-map --------------
Function fn_704;
Value *arityImpl_705(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_603(empty_list, arg0, (Value *)&_num_2);
Value *rslt4;
if((var_632)->type != 3) {
rslt4 = protoFnImpl_5(empty_list, var_632, rslt0);
} else {
FnArity *arity1 = findFnArity(var_632, 1);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
rslt4 = fn3(arity1->closures, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_632)->name);
  abort();
}
}
incRef(rslt4);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};

// --------- hash-map main body --------------
Function fn_704 = {3, -1, "hash-map", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_705}}};

SubString _kw_4 = {5, -1, 10, 0, ":not-found"};

// --------- merge-with --------------
Function fn_707;

// --------- anon --------------
Function fn_709;

// --------- anon --------------
Function fn_711;
Value *arityImpl_712(List *closures, Value *arg0, Value *arg1) {
Value *val5 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt13 = protoFnImpl_290(empty_list, arg1);
Value *rslt14 = arityImpl_378(empty_list, (Value *)&_num_2, rslt13);
Value *rslt15 = arityImpl_369(empty_list, rslt14);
decRef(rslt13);
my_free(rslt13);
decRef(rslt14);
my_free(rslt14);
decRef(rslt15);
my_free(rslt15);

if (isTrue(rslt15)) {
decRef(rslt15);
my_free(rslt15);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt15);
my_free(rslt15);
Value *rslt1 = arityImpl_609(empty_list, arg1, (Value *)&_num_9);
Value *rslt2 = arityImpl_609(empty_list, arg1, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_356(empty_list, arg0, rslt1, (Value *)&_kw_4);
Value *cond4;
Value *rslt11 = arityImpl_378(empty_list, (Value *)&_kw_4, rslt3);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_350(empty_list, arg0, rslt1, rslt2);
incRef(rslt12);
cond4 = rslt12;
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt11);
my_free(rslt11);
Value *rslt9;
if((val5)->type != 3) {
rslt9 = protoFnImpl_7(empty_list, val5, rslt3, rslt2);
} else {
FnArity *arity6 = findFnArity(val5, 2);
if(arity6 != (FnArity *)0 && !arity6->variadic) {
FnType2 *fn8 = (FnType2 *)arity6->fn;
rslt9 = fn8(arity6->closures, rslt3, rslt2);
} else if(arity6 != (FnArity *)0 && arity6->variadic) {
FnType1 *fn8 = (FnType1 *)arity6->fn;
List *varArgs7 = empty_list;
incRef(rslt2);
varArgs7 = (List *)listCons(rslt2, varArgs7);
incRef(rslt3);
varArgs7 = (List *)listCons(rslt3, varArgs7);
rslt9 = fn8(arity6->closures, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val5)->name);
  abort();
}
}
Value *rslt10 = protoFnImpl_350(empty_list, arg0, rslt1, rslt9);
incRef(rslt10);
cond4 = rslt10;
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);
}
incRef(cond4);
cond0 = cond4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(cond4);
my_free(cond4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *arityImpl_710(List *closures, Value *arg0, Value *arg1) {
Value *val2 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt0 = protoFnImpl_309(empty_list, arg1);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_712;
incRef((Value *)val2);
arity_1->closures = listCons((Value *)val2, (List *)arity_1->closures);
Function *fn_711 = malloc_function(1);
fn_711->type = 3;
fn_711->name = "anon";
fn_711->arityCount = 1;
fn_711->arities[0] = arity_1;
Value *rslt3 = arityImpl_392(empty_list, rslt0, arg0, (Value *)fn_711);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef((Value *)fn_711);
my_free((Value *)fn_711);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *arityImpl_708(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_274(empty_list, arg2);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef(arg1);
cond0 = arg1;
} else {
decRef(rslt3);
my_free(rslt3);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_710;
incRef((Value *)arg0);
arity_1->closures = listCons((Value *)arg0, (List *)arity_1->closures);
Function *fn_709 = malloc_function(1);
fn_709->type = 3;
fn_709->name = "anon";
fn_709->arityCount = 1;
fn_709->arities[0] = arity_1;
Value *rslt2 = arityImpl_392(empty_list, arg2, arg1, (Value *)fn_709);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_709);
my_free((Value *)fn_709);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- merge-with main body --------------
Function fn_707 = {3, -1, "merge-with", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_708}}};

SubString _kw_5 = {5, -1, 17, 0, ":get-in-not-found"};

// --------- get-in --------------
Function fn_714;
Value *arityImpl_715(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt7 = protoFnImpl_290(empty_list, arg1);
Value *rslt8 = arityImpl_378(empty_list, rslt7, (Value *)&_num_9);
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef(arg2);
cond0 = arg2;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt9 = protoFnImpl_290(empty_list, arg1);
Value *rslt10 = arityImpl_378(empty_list, rslt9, (Value *)&_num_1);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
Value *rslt11 = protoFnImpl_314(empty_list, arg1);
Value *rslt12 = protoFnImpl_356(empty_list, arg0, rslt11, arg2);
incRef(rslt12);
cond0 = rslt12;
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_314(empty_list, arg1);
Value *rslt2 = protoFnImpl_356(empty_list, arg0, rslt1, (Value *)&_kw_5);
Value *cond3;
Value *rslt6 = arityImpl_378(empty_list, (Value *)&_kw_5, rslt2);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(arg2);
cond3 = arg2;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt4 = protoFnImpl_319(empty_list, arg1);
Value *rslt5 = arityImpl_715(closures, rslt2, rslt4, arg2);
incRef(rslt5);
cond3 = rslt5;
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
}
incRef(cond3);
cond0 = cond3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(cond3);
my_free(cond3);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- get-in main body --------------
Function fn_714 = {3, -1, "get-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_715}}};

SubString _kw_6 = {5, -1, 14, 0, ":update-in-nil"};

// --------- update-in --------------
Function fn_717;
Value *arityImpl_718(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt8 = protoFnImpl_290(empty_list, arg1);
Value *rslt9 = arityImpl_378(empty_list, rslt8, (Value *)&_num_9);
decRef(rslt8);
my_free(rslt8);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_290(empty_list, arg1);
Value *rslt11 = arityImpl_378(empty_list, rslt10, (Value *)&_num_1);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_314(empty_list, arg1);
Value *rslt13 = protoFnImpl_356(empty_list, arg0, rslt12, (Value *)&_kw_6);
Value *cond14;
Value *rslt20 = arityImpl_378(empty_list, (Value *)&_kw_6, rslt13);
decRef(rslt20);
my_free(rslt20);

if (isTrue(rslt20)) {
decRef(rslt20);
my_free(rslt20);
incRef(arg0);
cond14 = arg0;
} else {
decRef(rslt20);
my_free(rslt20);
Value *rslt18;
if((arg2)->type != 3) {
rslt18 = protoFnImpl_5(empty_list, arg2, rslt13);
} else {
FnArity *arity15 = findFnArity(arg2, 1);
if(arity15 != (FnArity *)0 && !arity15->variadic) {
FnType1 *fn17 = (FnType1 *)arity15->fn;
rslt18 = fn17(arity15->closures, rslt13);
} else if(arity15 != (FnArity *)0 && arity15->variadic) {
FnType1 *fn17 = (FnType1 *)arity15->fn;
List *varArgs16 = empty_list;
incRef(rslt13);
varArgs16 = (List *)listCons(rslt13, varArgs16);
rslt18 = fn17(arity15->closures, (Value *)varArgs16);
decRef((Value *)varArgs16);
my_free((Value *)varArgs16);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg2)->name);
  abort();
}
}
Value *rslt19 = protoFnImpl_350(empty_list, arg0, rslt12, rslt18);
incRef(rslt19);
cond14 = rslt19;
decRef(rslt18);
my_free(rslt18);
decRef(rslt19);
my_free(rslt19);
}
incRef(cond14);
cond0 = cond14;
decRef(rslt12);
my_free(rslt12);
decRef(rslt13);
my_free(rslt13);
decRef(cond14);
my_free(cond14);
} else {
decRef(rslt11);
my_free(rslt11);
Value *rslt1 = protoFnImpl_314(empty_list, arg1);
Value *rslt2 = protoFnImpl_356(empty_list, arg0, rslt1, (Value *)&_kw_6);
Value *cond3;
Value *rslt7 = arityImpl_378(empty_list, (Value *)&_kw_6, rslt2);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(arg0);
cond3 = arg0;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt4 = protoFnImpl_319(empty_list, arg1);
Value *rslt5 = arityImpl_718(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_350(empty_list, arg0, rslt1, rslt5);
incRef(rslt6);
cond3 = rslt6;
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
}
incRef(cond3);
cond0 = cond3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(cond3);
my_free(cond3);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- update-in main body --------------
Function fn_717 = {3, -1, "update-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_718}}};

SubString _kw_7 = {5, -1, 13, 0, ":assoc-in-nil"};

// --------- assoc-in --------------
Function fn_720;
Value *arityImpl_721(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt13 = protoFnImpl_290(empty_list, arg1);
Value *rslt14 = arityImpl_378(empty_list, rslt13, (Value *)&_num_9);
decRef(rslt13);
my_free(rslt13);
decRef(rslt14);
my_free(rslt14);

if (isTrue(rslt14)) {
decRef(rslt14);
my_free(rslt14);
incRef(arg0);
cond0 = arg0;
} else {
decRef(rslt14);
my_free(rslt14);
Value *rslt15 = protoFnImpl_290(empty_list, arg1);
Value *rslt16 = arityImpl_378(empty_list, rslt15, (Value *)&_num_1);
decRef(rslt15);
my_free(rslt15);
decRef(rslt16);
my_free(rslt16);

if (isTrue(rslt16)) {
decRef(rslt16);
my_free(rslt16);
Value *rslt17 = protoFnImpl_314(empty_list, arg1);
Value *rslt18 = protoFnImpl_350(empty_list, arg0, rslt17, arg2);
incRef(rslt18);
cond0 = rslt18;
decRef(rslt17);
my_free(rslt17);
decRef(rslt18);
my_free(rslt18);
} else {
decRef(rslt16);
my_free(rslt16);
Value *rslt1 = protoFnImpl_314(empty_list, arg1);
Value *rslt2 = protoFnImpl_356(empty_list, arg0, rslt1, (Value *)&_kw_7);
Value *cond3;
Value *rslt7 = arityImpl_378(empty_list, (Value *)&_kw_7, rslt2);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
List *varArgs8 = empty_list;
Value *rslt9 = arityImpl_705(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_319(empty_list, arg1);
Value *rslt11 = arityImpl_721(closures, rslt9, rslt10, arg2);
Value *rslt12 = protoFnImpl_350(empty_list, arg0, rslt1, rslt11);
incRef(rslt12);
cond3 = rslt12;
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt4 = protoFnImpl_319(empty_list, arg1);
Value *rslt5 = arityImpl_721(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_350(empty_list, arg0, rslt1, rslt5);
incRef(rslt6);
cond3 = rslt6;
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
}
incRef(cond3);
cond0 = cond3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(cond3);
my_free(cond3);
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- assoc-in main body --------------
Function fn_720 = {3, -1, "assoc-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_721}}};


// --------- =*_impl --------------
Function fn_723;
Value *arityImpl_724(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt1 = arityImpl_61(empty_list, arg1);
Value *rslt2 = arityImpl_378(empty_list, rslt0, rslt1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_723 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_724}}};

Value *protoImpl_725(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_726 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_725}}};

ReifiedVal reified_727 = {13, -1, 1, {(Value *)&fn_723}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[19];} _str_40 = {1, -1, 18,"Could not look up "};

// --------- =*_impl --------------
Function fn_729;
Value *arityImpl_730(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_118(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_729 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_730}}};


// --------- name_impl --------------
Function fn_731;
Value *arityImpl_732(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_46(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_731 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_732}}};


// --------- string-list_impl --------------
Function fn_733;
Value *arityImpl_734(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_226(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_733 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_734}}};


// --------- invoke_impl --------------
Function fn_735;
Value *arityImpl_736(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_356(empty_list, arg1, arg0, (Value *)&reified_727);
Value *cond1;
Value *rslt2 = arityImpl_378(empty_list, (Value *)&reified_727, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_40);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_40, varArgs3);
Value *rslt4 = arityImpl_258(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_58(empty_list);
incRef(rslt5);
cond1 = rslt5;
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
} else {
decRef(rslt2);
my_free(rslt2);
incRef(rslt0);
cond1 = rslt0;
}
incRef(cond1);
decRef(rslt0);
my_free(rslt0);
decRef(cond1);
my_free(cond1);
return(cond1);
};


// --------- invoke_impl main body --------------
Function fn_735 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_736}}};


// --------- =*_impl --------------
Function fn_737;
Value *arityImpl_738(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_118(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_737 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_738}}};


// --------- name_impl --------------
Function fn_739;
Value *arityImpl_740(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_46(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_739 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_740}}};


// --------- string-list_impl --------------
Function fn_741;
Value *arityImpl_742(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_226(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_212(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_741 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_742}}};


// --------- invoke_impl --------------
Function fn_743;
Value *arityImpl_744(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_356(empty_list, arg1, arg0, (Value *)&reified_727);
Value *cond1;
Value *rslt2 = arityImpl_378(empty_list, (Value *)&reified_727, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_40);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_40, varArgs3);
Value *rslt4 = arityImpl_258(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_58(empty_list);
incRef(rslt5);
cond1 = rslt5;
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
} else {
decRef(rslt2);
my_free(rslt2);
incRef(rslt0);
cond1 = rslt0;
}
incRef(cond1);
decRef(rslt0);
my_free(rslt0);
decRef(cond1);
my_free(cond1);
return(cond1);
};


// --------- invoke_impl main body --------------
Function fn_743 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_744}}};


// --------- invoke_impl --------------
Function fn_745;
Value *arityImpl_746(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_356(empty_list, arg1, arg0, arg2);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- invoke_impl main body --------------
Function fn_745 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_746}}};


// --------- symbol? --------------
Function fn_747;
Value *arityImpl_748(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_7, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- symbol? main body --------------
Function fn_747 = {3, -1, "symbol?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_748}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_41 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_750;
Value *arityImpl_751(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_41);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_41, varArgs0);
Value *rslt1 = arityImpl_580(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_55(empty_list, rslt1);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- keyword main body --------------
Function fn_750 = {3, -1, "keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_751}}};


// --------- keyword? --------------
Function fn_753;
Value *arityImpl_754(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_5, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- keyword? main body --------------
Function fn_753 = {3, -1, "keyword?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_754}}};


// --------- number? --------------
Function fn_756;
Value *arityImpl_757(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_2, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- number? main body --------------
Function fn_756 = {3, -1, "number?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_757}}};


// --------- string? --------------
Function fn_759;
Value *arityImpl_760(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_61(empty_list, arg0);
Value *rslt1 = arityImpl_378(empty_list, (Value *)&_num_1, rslt0);
Value *rslt2 = arityImpl_61(empty_list, arg0);
Value *rslt3 = arityImpl_378(empty_list, (Value *)&_num_6, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)rslt1);
varArgs4 = (List *)listCons((Value *)rslt1, varArgs4);
Value *rslt5 = arityImpl_375(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};


// --------- string? main body --------------
Function fn_759 = {3, -1, "string?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_760}}};


// --------- range* --------------
Function fn_762;
Value *arityImpl_763(List *closures, Value *arg0) {
Value *cond0;
Value *rslt4 = arityImpl_378(empty_list, (Value *)&_num_9, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_num_9);
varArgs5 = (List *)listCons((Value *)(Value *)&_num_9, varArgs5);
Value *rslt6 = arityImpl_212(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = arityImpl_526(empty_list, arg0);
Value *rslt2 = arityImpl_763(closures, rslt1);
Value *rslt3 = arityImpl_94(empty_list, arg0, rslt2);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt3);
my_free(rslt3);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- range* main body --------------
Function fn_762 = {3, -1, "range*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_763}}};


// --------- range --------------
Function fn_765;
Value *arityImpl_766(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_526(empty_list, arg0);
Value *rslt1 = arityImpl_763(empty_list, rslt0);
Value *rslt2 = arityImpl_403(empty_list, rslt1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- range main body --------------
Function fn_765 = {3, -1, "range", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_766}}};


// --------- repeat --------------
Function fn_768;

// --------- anon --------------
Function fn_770;
Value *arityImpl_771(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *arityImpl_769(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_382(empty_list, arg0, (Value *)&_num_1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_91);
cond0 = var_91;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_526(empty_list, arg0);
Value *rslt2 = arityImpl_763(empty_list, rslt1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_771;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_770 = malloc_function(1);
fn_770->type = 3;
fn_770->name = "anon";
fn_770->arityCount = 1;
fn_770->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_220(empty_list, rslt2, (Value *)fn_770);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_770);
my_free((Value *)fn_770);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- repeat main body --------------
Function fn_768 = {3, -1, "repeat", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_769}}};

SubString _kw_8 = {5, -1, 6, 0, ":bogus"};

int main_773 (Value *arg0) {

return(0);
}

ProtoImpls localImpls_774 = {4, (Value *)0, {{9, (Value *)&protoFn_452}, {11, (Value *)&protoFn_702}, {5, (Value *)&fn_735}, {7, (Value *)&fn_745}}};
ProtoImpls localImpls_775 = {0, (Value *)0, {}};
ProtoImpls localImpls_776 = {0, (Value *)&defaultFn_148, {}};
ProtoImpls localImpls_777 = {2, (Value *)0, {{9, (Value *)&protoFn_438}, {11, (Value *)&protoFn_636}}};
ProtoImpls localImpls_778 = {1, (Value *)&defaultFn_161, {{4, (Value *)&fn_511}}};
ProtoImpls localImpls_779 = {0, (Value *)&defaultFn_167, {}};
ProtoImpls localImpls_780 = {0, (Value *)0, {}};
ProtoImpls localImpls_781 = {0, (Value *)0, {}};
ProtoImpls localImpls_782 = {0, (Value *)0, {}};
ProtoImpls localImpls_783 = {1, (Value *)&defaultFn_191, {{4, (Value *)&fn_509}}};
ProtoImpls localImpls_784 = {2, (Value *)&defaultFn_197, {{3, (Value *)&fn_418}, {10, (Value *)&protoFn_446}}};
ProtoImpls localImpls_785 = {1, (Value *)&defaultFn_216, {{4, (Value *)&fn_507}}};
ProtoImpls localImpls_786 = {2, (Value *)&defaultFn_224, {{5, (Value *)&fn_731}, {7, (Value *)&fn_739}}};
ProtoImpls localImpls_787 = {8, (Value *)&defaultFn_230, {{3, (Value *)&fn_408}, {2, (Value *)&fn_424}, {4, (Value *)&fn_485}, {1, (Value *)&fn_547}, {6, (Value *)&fn_555}, {12, (Value *)&protoFn_660}, {5, (Value *)&fn_733}, {7, (Value *)&fn_741}}};
ProtoImpls localImpls_788 = {0, (Value *)&defaultFn_236, {}};
ProtoImpls localImpls_789 = {8, (Value *)&defaultFn_261, {{2, (Value *)&fn_420}, {4, (Value *)&fn_483}, {1, (Value *)&fn_531}, {6, (Value *)&fn_557}, {12, (Value *)&protoFn_654}, {13, (Value *)&protoFn_726}, {5, (Value *)&fn_729}, {7, (Value *)&fn_737}}};
ProtoImpls localImpls_790 = {1, (Value *)&defaultFn_267, {{2, (Value *)&fn_422}}};
ProtoImpls localImpls_791 = {4, (Value *)0, {{4, (Value *)&fn_487}, {1, (Value *)&fn_533}, {6, (Value *)&fn_559}, {12, (Value *)&protoFn_664}}};
ProtoImpls localImpls_792 = {3, (Value *)0, {{4, (Value *)&fn_489}, {1, (Value *)&fn_535}, {6, (Value *)&fn_561}}};
ProtoImpls localImpls_793 = {0, (Value *)0, {}};
ProtoImpls localImpls_794 = {4, (Value *)&defaultFn_288, {{4, (Value *)&fn_493}, {1, (Value *)&fn_537}, {6, (Value *)&fn_563}, {12, (Value *)&protoFn_668}}};
ProtoImpls localImpls_795 = {3, (Value *)0, {{4, (Value *)&fn_491}, {1, (Value *)&fn_539}, {6, (Value *)&fn_565}}};
ProtoImpls localImpls_796 = {1, (Value *)&defaultFn_302, {{4, (Value *)&fn_495}}};
ProtoImpls localImpls_797 = {4, (Value *)0, {{4, (Value *)&fn_497}, {1, (Value *)&fn_541}, {6, (Value *)&fn_567}, {12, (Value *)&protoFn_642}}};
ProtoImpls localImpls_798 = {4, (Value *)0, {{4, (Value *)&fn_499}, {1, (Value *)&fn_543}, {6, (Value *)&fn_569}, {12, (Value *)&protoFn_646}}};
ProtoImpls localImpls_799 = {4, (Value *)0, {{4, (Value *)&fn_501}, {1, (Value *)&fn_545}, {6, (Value *)&fn_571}, {12, (Value *)&protoFn_650}}};
ProtoImpls localImpls_800 = {1, (Value *)0, {{4, (Value *)&fn_481}}};
ProtoImpls localImpls_801 = {1, (Value *)0, {{4, (Value *)&fn_477}}};
ProtoImpls localImpls_802 = {3, (Value *)0, {{3, (Value *)&fn_410}, {4, (Value *)&fn_503}, {12, (Value *)&protoFn_672}}};
ProtoImpls localImpls_803 = {5, (Value *)0, {{3, (Value *)&fn_412}, {4, (Value *)&fn_505}, {1, (Value *)&fn_549}, {6, (Value *)&fn_573}, {12, (Value *)&protoFn_680}}};
ProtoImpls localImpls_804 = {1, (Value *)0, {{12, (Value *)&protoFn_684}}};
ProtoImpls localImpls_805 = {1, (Value *)&defaultFn_354, {{12, (Value *)&protoFn_688}}};
ProtoImpls localImpls_806 = {1, (Value *)0, {{12, (Value *)&protoFn_692}}};
ProtoImpls localImpls_807 = {1, (Value *)0, {{12, (Value *)&protoFn_696}}};
ProtoImpls localImpls_808 = {1, (Value *)0, {{10, (Value *)&protoFn_450}}};
ProtoImpls localImpls_809 = {1, (Value *)0, {{12, (Value *)&protoFn_700}}};

int toccataMain(int argc, char *argv[]) {
  protoImpls_0 = &localImpls_774;
  protoImpls_141 = &localImpls_775;
  protoImpls_146 = &localImpls_776;
  protoImpls_154 = &localImpls_777;
  protoImpls_159 = &localImpls_778;
  protoImpls_165 = &localImpls_779;
  protoImpls_173 = &localImpls_780;
  protoImpls_178 = &localImpls_781;
  protoImpls_183 = &localImpls_782;
  protoImpls_189 = &localImpls_783;
  protoImpls_195 = &localImpls_784;
  protoImpls_214 = &localImpls_785;
  protoImpls_222 = &localImpls_786;
  protoImpls_228 = &localImpls_787;
  protoImpls_234 = &localImpls_788;
  protoImpls_259 = &localImpls_789;
  protoImpls_265 = &localImpls_790;
  protoImpls_271 = &localImpls_791;
  protoImpls_276 = &localImpls_792;
  protoImpls_281 = &localImpls_793;
  protoImpls_286 = &localImpls_794;
  protoImpls_292 = &localImpls_795;
  protoImpls_300 = &localImpls_796;
  protoImpls_306 = &localImpls_797;
  protoImpls_311 = &localImpls_798;
  protoImpls_316 = &localImpls_799;
  protoImpls_324 = &localImpls_800;
  protoImpls_329 = &localImpls_801;
  protoImpls_334 = &localImpls_802;
  protoImpls_339 = &localImpls_803;
  protoImpls_347 = &localImpls_804;
  protoImpls_352 = &localImpls_805;
  protoImpls_358 = &localImpls_806;
  protoImpls_363 = &localImpls_807;
  protoImpls_429 = &localImpls_808;
  protoImpls_627 = &localImpls_809;
#ifndef REF_COUNT
    GC_init();
#endif
     outStream = stdout;
     List *argList = malloc_list();
      argList->type = ListType;
      argList->len = 0;
      argList->head = (Value *)0;
      argList->tail = (List *)0;
      List *tail = argList;
      for(int i = 0; i < argc; i++) {
         List *newTail = malloc_list();
         newTail->type = ListType;
         newTail->len = 0;
         newTail->tail = (List *)0;
         newTail->head = (Value *)0;
         tail->head = stringValue(argv[i]);
         tail->tail = newTail;
         tail = newTail;
         argList->len++;
}
  int the_final_answer = main_773((Value *)argList);
  decRef((Value *)argList);
  my_free((Value *)argList);
  fprintf(stderr, "malloc count: %lld  free count: %lld  diff: %lld\n", malloc_count, free_count, malloc_count - free_count);
  return(the_final_answer);
};
Value *symbol_literals() {
List *syms = empty_list;
List *symInfo;
return((Value *)syms);
}

Value *number_literals() {
List *nums = empty_list;
List *numInfo;
numInfo = listCons(stringValue("_num_1"), empty_list);
numInfo = listCons(numberValue(1), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_2"), empty_list);
numInfo = listCons(numberValue(2), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_3"), empty_list);
numInfo = listCons(numberValue(3), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_4"), empty_list);
numInfo = listCons(numberValue(4), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_5"), empty_list);
numInfo = listCons(numberValue(5), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_6"), empty_list);
numInfo = listCons(numberValue(6), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_7"), empty_list);
numInfo = listCons(numberValue(7), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_8"), empty_list);
numInfo = listCons(numberValue(8), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_9"), empty_list);
numInfo = listCons(numberValue(0), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_10"), empty_list);
numInfo = listCons(numberValue(10), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_11"), empty_list);
numInfo = listCons(numberValue(12), numInfo);
nums = listCons((Value *)numInfo, nums);
return((Value *)nums);
}

Value *string_literals() {
List *strs = empty_list;
List *strInfo;
strInfo = listCons(stringValue("_str_0"), empty_list);
strInfo = listCons(stringValue("void"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_1"), empty_list);
strInfo = listCons(stringValue("char"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_2"), empty_list);
strInfo = listCons(stringValue("char *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_3"), empty_list);
strInfo = listCons(stringValue("int"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_4"), empty_list);
strInfo = listCons(stringValue("int64_t"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_5"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs;} Value;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_6"), empty_list);
strInfo = listCons(stringValue("Value *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_7"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_8"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_9"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_10"), empty_list);
strInfo = listCons(stringValue("typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_11"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_12"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_13"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_14"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_15"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_16"), empty_list);
strInfo = listCons(stringValue(":match*-one-arg"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_17"), empty_list);
strInfo = listCons(stringValue(":match*-two-args"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_18"), empty_list);
strInfo = listCons(stringValue("*** 'flat-map' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_19"), empty_list);
strInfo = listCons(stringValue("*** 'wrap' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_20"), empty_list);
strInfo = listCons(stringValue("'name' not implemented for type "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_21"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_22"), empty_list);
strInfo = listCons(stringValue("'serialize' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_23"), empty_list);
strInfo = listCons(stringValue(" "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_24"), empty_list);
strInfo = listCons(stringValue("\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_25"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_26"), empty_list);
strInfo = listCons(stringValue("'=*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_27"), empty_list);
strInfo = listCons(stringValue("'<*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_28"), empty_list);
strInfo = listCons(stringValue("'count' not implemented for "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_29"), empty_list);
strInfo = listCons(stringValue("'get' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_30"), empty_list);
strInfo = listCons(stringValue("<Fn: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_31"), empty_list);
strInfo = listCons(stringValue(">"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_32"), empty_list);
strInfo = listCons(stringValue("("), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_33"), empty_list);
strInfo = listCons(stringValue(", "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_34"), empty_list);
strInfo = listCons(stringValue(")"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_35"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_36"), empty_list);
strInfo = listCons(stringValue("'nth' from empty seq"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_37"), empty_list);
strInfo = listCons(stringValue("{}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_38"), empty_list);
strInfo = listCons(stringValue("{"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue("}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_40"), empty_list);
strInfo = listCons(stringValue("Could not look up "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
strInfo = listCons(stringValue(":"), strInfo);
strs = listCons((Value *)strInfo, strs);
return((Value *)strs);
}

Value *keyword_literals() {
List *kws = empty_list;
List *kwInfo;
kwInfo = listCons(stringValue("_kw_0"), empty_list);
kwInfo = listCons(keywordValue(":m"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_1"), empty_list);
kwInfo = listCons(keywordValue(":k"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_2"), empty_list);
kwInfo = listCons(keywordValue(":nil"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_3"), empty_list);
kwInfo = listCons(keywordValue(":hm-nf"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_4"), empty_list);
kwInfo = listCons(keywordValue(":not-found"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_5"), empty_list);
kwInfo = listCons(keywordValue(":get-in-not-found"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_6"), empty_list);
kwInfo = listCons(keywordValue(":update-in-nil"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_7"), empty_list);
kwInfo = listCons(keywordValue(":assoc-in-nil"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_8"), empty_list);
kwInfo = listCons(keywordValue(":bogus"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
return((Value *)kws);
}

Value *protocols() {
List *protos = empty_list;
List *protoInfo;
List *impls;
List *impl;
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_452"), impl);
impl = listCons(numberValue(9), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_702"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_735"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_745"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_1;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_0"), protoInfo);
protoInfo = listCons(symbolValue("invoke"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_142;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_141"), protoInfo);
protoInfo = listCons(symbolValue("bippity"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_148"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_147;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_146"), protoInfo);
protoInfo = listCons(symbolValue("match*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_438"), impl);
impl = listCons(numberValue(9), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_636"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_155;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_154"), protoInfo);
protoInfo = listCons(symbolValue("instance?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_161"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_511"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_160;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_159"), protoInfo);
protoInfo = listCons(symbolValue("flat-map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_167"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_166;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_165"), protoInfo);
protoInfo = listCons(symbolValue("flatten"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_174;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_173"), protoInfo);
protoInfo = listCons(symbolValue("extract"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_179;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_178"), protoInfo);
protoInfo = listCons(symbolValue("extend"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_184;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_183"), protoInfo);
protoInfo = listCons(symbolValue("duplicate"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_191"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_509"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_190;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_189"), protoInfo);
protoInfo = listCons(symbolValue("wrap"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_197"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_418"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_446"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_196;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_195"), protoInfo);
protoInfo = listCons(symbolValue("apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_216"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_507"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_215;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_214"), protoInfo);
protoInfo = listCons(symbolValue("map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_224"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_731"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_739"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_223;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_222"), protoInfo);
protoInfo = listCons(symbolValue("name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_230"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_408"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_424"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_485"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_547"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_555"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_660"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_733"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_741"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_229;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_228"), protoInfo);
protoInfo = listCons(symbolValue("string-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_236"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_235;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_234"), protoInfo);
protoInfo = listCons(symbolValue("serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_261"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_420"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_483"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_531"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_557"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_654"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_726"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_729"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_737"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_260;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_259"), protoInfo);
protoInfo = listCons(symbolValue("=*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_267"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_422"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_266;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_265"), protoInfo);
protoInfo = listCons(symbolValue("<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_487"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_533"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_559"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_664"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_272;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_271"), protoInfo);
protoInfo = listCons(symbolValue("empty?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_489"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_535"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_561"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_277;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_276"), protoInfo);
protoInfo = listCons(symbolValue("empty"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_282;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_281"), protoInfo);
protoInfo = listCons(symbolValue("destruct"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_288"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_493"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_537"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_563"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_668"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_287;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_286"), protoInfo);
protoInfo = listCons(symbolValue("count"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_491"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_539"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_565"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_293;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_292"), protoInfo);
protoInfo = listCons(symbolValue("conj"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_302"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_495"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_301;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_300"), protoInfo);
protoInfo = listCons(symbolValue("seq?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_497"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_541"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_567"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_642"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_307;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_306"), protoInfo);
protoInfo = listCons(symbolValue("seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_499"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_543"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_569"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_646"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_312;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_311"), protoInfo);
protoInfo = listCons(symbolValue("first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_501"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_545"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_571"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_650"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_317;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_316"), protoInfo);
protoInfo = listCons(symbolValue("rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_481"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_325;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_324"), protoInfo);
protoInfo = listCons(symbolValue("traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_477"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_330;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_329"), protoInfo);
protoInfo = listCons(symbolValue("crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_410"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_503"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_672"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_335;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_334"), protoInfo);
protoInfo = listCons(symbolValue("zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_412"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_505"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_549"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_573"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_680"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_340;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_339"), protoInfo);
protoInfo = listCons(symbolValue("comp*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_684"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_348;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_347"), protoInfo);
protoInfo = listCons(symbolValue("assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_354"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_688"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_353;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_352"), protoInfo);
protoInfo = listCons(symbolValue("get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_692"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_359;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_358"), protoInfo);
protoInfo = listCons(symbolValue("keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_696"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_364;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_363"), protoInfo);
protoInfo = listCons(symbolValue("vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_450"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_430;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_429"), protoInfo);
protoInfo = listCons(symbolValue(".v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_700"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_628;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_627"), protoInfo);
protoInfo = listCons(symbolValue(".a-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
return((Value *)protos);
}

Value *static_fns() {
List *staticFns = empty_list;
List *fnInfo;
List *arityInfo;
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_3"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_5"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_7"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_9"), empty_list);
arityInfo = listCons(numberValue(4), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_11"), empty_list);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_13"), empty_list);
arityInfo = listCons(numberValue(6), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_15"), empty_list);
arityInfo = listCons(numberValue(7), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_17"), empty_list);
arityInfo = listCons(numberValue(8), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_1"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_40"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_39"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_43"), empty_list);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_42"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_46"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_45"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_49"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_48"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_52"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_51"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_55"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_54"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_58"), empty_list);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_57"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_61"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_60"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_64"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_63"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_67"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_68"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_66"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_71"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_70"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_74"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_73"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_77"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_76"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_80"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_79"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_83"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_82"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_86"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_85"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_89"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_88"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_93"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_94"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_92"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_97"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_96"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_100"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_99"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_103"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_102"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_106"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_105"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_109"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_108"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_112"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_111"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_115"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_114"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_118"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_117"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_121"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_120"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_124"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_123"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_127"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_126"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_130"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_129"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_133"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_132"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_136"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_135"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_139"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_138"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_144"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_142"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_150"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_152"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_147"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_157"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_155"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_163"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_160"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_170"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_169"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_171"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_166"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_176"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_174"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_181"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_179"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_186"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_184"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_193"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_190"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_203"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_196"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_206"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_205"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_209"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_208"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_212"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_211"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_220"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_215"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_226"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_223"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_232"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_229"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_238"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_235"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_241"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_240"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_244"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_243"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_249"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_248"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_252"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_251"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_255"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_254"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_258"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_257"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_263"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_260"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_269"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_266"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_274"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_272"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_279"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_277"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_284"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_282"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_290"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_287"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_295"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_293"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_298"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_297"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_304"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_301"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_309"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_307"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_314"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_312"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_319"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_317"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_322"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_321"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_327"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_325"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_332"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_330"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_337"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_335"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_342"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_340"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_345"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_344"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_350"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_348"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_356"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_353"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_361"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_359"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_366"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_364"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_369"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_368"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_372"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_371"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_375"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_374"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_378"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_379"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_377"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_382"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_383"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_381"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_386"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_385"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_389"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_388"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_392"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_391"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_395"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_394"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_398"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_397"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_403"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_402"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_406"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_405"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_409"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_408"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_411"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_410"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_417"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_416"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_413"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_412"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_419"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_418"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_421"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_420"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_423"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_422"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_425"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_424"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_427"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_426"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_432"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_430"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_436"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_435"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_444"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_443"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_440"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_439"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_455"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_454"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_464"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_463"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_460"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_459"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_470"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_469"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_475"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_474"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_473"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_472"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_478"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_477"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_482"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_481"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_484"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_483"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_486"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_485"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_488"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_487"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_490"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_489"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_492"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_491"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_494"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_493"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_496"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_495"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_498"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_497"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_500"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_499"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_502"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_501"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_504"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_503"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_506"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_505"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_508"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_507"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_510"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_509"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_512"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_511"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_514"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_513"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_517"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_516"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_520"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_519"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_523"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_522"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_526"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_525"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_529"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_528"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_532"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_531"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_534"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_533"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_536"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_535"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_538"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_537"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_540"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_539"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_542"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_541"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_544"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_543"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_546"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_545"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_548"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_547"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_552"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_551"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_550"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_549"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_556"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_555"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_558"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_557"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_560"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_559"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_562"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_561"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_564"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_563"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_566"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_565"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_568"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_567"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_570"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_569"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_572"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_571"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_576"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_575"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_574"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_573"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_582"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_581"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_580"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_579"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_587"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_586"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_590"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_589"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_593"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_594"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_592"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_597"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_596"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_600"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_599"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_603"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_602"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_606"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_605"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_609"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_610"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_608"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_613"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_612"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_616"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_615"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_619"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_618"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_622"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_621"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_625"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_624"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_630"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_628"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_634"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_633"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_658"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_657"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_670"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_669"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_678"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_677"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_676"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_675"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_674"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_673"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_638"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_637"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_705"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_704"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_708"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_707"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_715"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_714"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_718"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_717"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_721"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_720"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_724"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_723"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_730"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_729"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_732"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_731"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_734"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_733"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_736"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_735"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_738"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_737"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_740"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_739"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_742"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_741"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_744"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_743"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_746"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_745"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_748"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_747"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_751"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_750"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_754"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_753"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_757"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_756"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_760"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_759"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_763"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_762"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_766"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_765"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_769"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_768"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
return((Value *)staticFns);
}

Value *defined_syms() {
List *defSyms = empty_list;
List *symInfo;
symInfo = listCons(stringValue("(Value *)&_num_1"), empty_list);
symInfo = listCons(stringValue("Number _num_1"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("String"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_2"), empty_list);
symInfo = listCons(stringValue("Number _num_2"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Number"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_3"), empty_list);
symInfo = listCons(stringValue("Number _num_3"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Function"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_4"), empty_list);
symInfo = listCons(stringValue("Number _num_4"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("List"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_5"), empty_list);
symInfo = listCons(stringValue("Number _num_5"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_6"), empty_list);
symInfo = listCons(stringValue("Number _num_6"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("SubStr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_7"), empty_list);
symInfo = listCons(stringValue("Number _num_7"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_8"), empty_list);
symInfo = listCons(stringValue("Number _num_8"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_1"), empty_list);
symInfo = listCons(stringValue("Function protoFn_1"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_257"), empty_list);
symInfo = listCons(stringValue("Function fn_257"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print-err"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_0"), empty_list);
symInfo = listCons(stringValue("String _str_0"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("VoidT"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_1"), empty_list);
symInfo = listCons(stringValue("String _str_1"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_2"), empty_list);
symInfo = listCons(stringValue("String _str_2"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_3"), empty_list);
symInfo = listCons(stringValue("String _str_3"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int32"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_4"), empty_list);
symInfo = listCons(stringValue("String _str_4"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int64"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_4"), empty_list);
symInfo = listCons(stringValue(""), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ValueType"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_5"), empty_list);
symInfo = listCons(stringValue("String _str_5"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_6"), empty_list);
symInfo = listCons(stringValue("String _str_6"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_7"), empty_list);
symInfo = listCons(stringValue("String _str_7"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("NumberVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_8"), empty_list);
symInfo = listCons(stringValue("String _str_8"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("StringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_9"), empty_list);
symInfo = listCons(stringValue("String _str_9"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("SubStringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_10"), empty_list);
symInfo = listCons(stringValue("String _str_10"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ListVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_11"), empty_list);
symInfo = listCons(stringValue("String _str_11"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArityVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_12"), empty_list);
symInfo = listCons(stringValue("String _str_12"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FunctionVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_13"), empty_list);
symInfo = listCons(stringValue("String _str_13"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_14"), empty_list);
symInfo = listCons(stringValue("String _str_14"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpls"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_15"), empty_list);
symInfo = listCons(stringValue("String _str_15"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ReifiedVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_37"), empty_list);
symInfo = listCons(stringValue("Value *var_37;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("true"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_38"), empty_list);
symInfo = listCons(stringValue("Value *var_38;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("false"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_39"), empty_list);
symInfo = listCons(stringValue("Function fn_39"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("output-to-file"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_42"), empty_list);
symInfo = listCons(stringValue("Function fn_42"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("standard-output"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_45"), empty_list);
symInfo = listCons(stringValue("Function fn_45"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_48"), empty_list);
symInfo = listCons(stringValue("Function fn_48"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char-code"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_51"), empty_list);
symInfo = listCons(stringValue("Function fn_51"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_54"), empty_list);
symInfo = listCons(stringValue("Function fn_54"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("new-keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_57"), empty_list);
symInfo = listCons(stringValue("Function fn_57"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("abort"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_60"), empty_list);
symInfo = listCons(stringValue("Function fn_60"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-type"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_63"), empty_list);
symInfo = listCons(stringValue("Function fn_63"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_66"), empty_list);
symInfo = listCons(stringValue("Function fn_66"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subs"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_70"), empty_list);
symInfo = listCons(stringValue("Function fn_70"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_73"), empty_list);
symInfo = listCons(stringValue("Function fn_73"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_76"), empty_list);
symInfo = listCons(stringValue("Function fn_76"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-less-than"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_79"), empty_list);
symInfo = listCons(stringValue("Function fn_79"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("add-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_82"), empty_list);
symInfo = listCons(stringValue("Function fn_82"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subtract-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_85"), empty_list);
symInfo = listCons(stringValue("Function fn_85"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("mult-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_88"), empty_list);
symInfo = listCons(stringValue("Function fn_88"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rem"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_91"), empty_list);
symInfo = listCons(stringValue("Value *var_91;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_92"), empty_list);
symInfo = listCons(stringValue("Function fn_92"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cons"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_96"), empty_list);
symInfo = listCons(stringValue("Function fn_96"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_99"), empty_list);
symInfo = listCons(stringValue("Function fn_99"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("car"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_102"), empty_list);
symInfo = listCons(stringValue("Function fn_102"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cdr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_105"), empty_list);
symInfo = listCons(stringValue("Function fn_105"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_108"), empty_list);
symInfo = listCons(stringValue("Function fn_108"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_111"), empty_list);
symInfo = listCons(stringValue("Function fn_111"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_114"), empty_list);
symInfo = listCons(stringValue("Function fn_114"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_117"), empty_list);
symInfo = listCons(stringValue("Function fn_117"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_120"), empty_list);
symInfo = listCons(stringValue("Function fn_120"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-malloc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_123"), empty_list);
symInfo = listCons(stringValue("Function fn_123"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-append"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_126"), empty_list);
symInfo = listCons(stringValue("Function fn_126"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr-err*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_129"), empty_list);
symInfo = listCons(stringValue("Function fn_129"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("slurp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_132"), empty_list);
symInfo = listCons(stringValue("Function fn_132"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_135"), empty_list);
symInfo = listCons(stringValue("Function fn_135"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("escape-chars"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_138"), empty_list);
symInfo = listCons(stringValue("Function fn_138"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_142"), empty_list);
symInfo = listCons(stringValue("Function protoFn_142"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("bippity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_147"), empty_list);
symInfo = listCons(stringValue("Function protoFn_147"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("match*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_155"), empty_list);
symInfo = listCons(stringValue("Function protoFn_155"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_160"), empty_list);
symInfo = listCons(stringValue("Function protoFn_160"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_770"), empty_list);
symInfo = listCons(stringValue("Function fn_770"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_166"), empty_list);
symInfo = listCons(stringValue("Function protoFn_166"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_174"), empty_list);
symInfo = listCons(stringValue("Function protoFn_174"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extract"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_179"), empty_list);
symInfo = listCons(stringValue("Function protoFn_179"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_184"), empty_list);
symInfo = listCons(stringValue("Function protoFn_184"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("duplicate"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_459"), empty_list);
symInfo = listCons(stringValue("Function fn_459"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comprehend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_190"), empty_list);
symInfo = listCons(stringValue("Function protoFn_190"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_196"), empty_list);
symInfo = listCons(stringValue("Function protoFn_196"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_205"), empty_list);
symInfo = listCons(stringValue("Function fn_205"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_208"), empty_list);
symInfo = listCons(stringValue("Function fn_208"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply-to"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_211"), empty_list);
symInfo = listCons(stringValue("Function fn_211"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_215"), empty_list);
symInfo = listCons(stringValue("Function protoFn_215"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_223"), empty_list);
symInfo = listCons(stringValue("Function protoFn_223"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_229"), empty_list);
symInfo = listCons(stringValue("Function protoFn_229"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_235"), empty_list);
symInfo = listCons(stringValue("Function protoFn_235"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_240"), empty_list);
symInfo = listCons(stringValue("Function fn_240"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_243"), empty_list);
symInfo = listCons(stringValue("Function fn_243"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_248"), empty_list);
symInfo = listCons(stringValue("Function fn_248"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("prn"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_251"), empty_list);
symInfo = listCons(stringValue("Function fn_251"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_254"), empty_list);
symInfo = listCons(stringValue("Function fn_254"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_260"), empty_list);
symInfo = listCons(stringValue("Function protoFn_260"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_266"), empty_list);
symInfo = listCons(stringValue("Function protoFn_266"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_272"), empty_list);
symInfo = listCons(stringValue("Function protoFn_272"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_277"), empty_list);
symInfo = listCons(stringValue("Function protoFn_277"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_282"), empty_list);
symInfo = listCons(stringValue("Function protoFn_282"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("destruct"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_287"), empty_list);
symInfo = listCons(stringValue("Function protoFn_287"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_293"), empty_list);
symInfo = listCons(stringValue("Function protoFn_293"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_297"), empty_list);
symInfo = listCons(stringValue("Function fn_297"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_301"), empty_list);
symInfo = listCons(stringValue("Function protoFn_301"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_307"), empty_list);
symInfo = listCons(stringValue("Function protoFn_307"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_312"), empty_list);
symInfo = listCons(stringValue("Function protoFn_312"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_317"), empty_list);
symInfo = listCons(stringValue("Function protoFn_317"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_321"), empty_list);
symInfo = listCons(stringValue("Function fn_321"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("second"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_325"), empty_list);
symInfo = listCons(stringValue("Function protoFn_325"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_330"), empty_list);
symInfo = listCons(stringValue("Function protoFn_330"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_335"), empty_list);
symInfo = listCons(stringValue("Function protoFn_335"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_340"), empty_list);
symInfo = listCons(stringValue("Function protoFn_340"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_344"), empty_list);
symInfo = listCons(stringValue("Function fn_344"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_348"), empty_list);
symInfo = listCons(stringValue("Function protoFn_348"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_353"), empty_list);
symInfo = listCons(stringValue("Function protoFn_353"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_359"), empty_list);
symInfo = listCons(stringValue("Function protoFn_359"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_364"), empty_list);
symInfo = listCons(stringValue("Function protoFn_364"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_368"), empty_list);
symInfo = listCons(stringValue("Function fn_368"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_371"), empty_list);
symInfo = listCons(stringValue("Function fn_371"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("and"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_374"), empty_list);
symInfo = listCons(stringValue("Function fn_374"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("or"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_377"), empty_list);
symInfo = listCons(stringValue("Function fn_377"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_381"), empty_list);
symInfo = listCons(stringValue("Function fn_381"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_385"), empty_list);
symInfo = listCons(stringValue("Function fn_385"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_388"), empty_list);
symInfo = listCons(stringValue("Function fn_388"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_391"), empty_list);
symInfo = listCons(stringValue("Function fn_391"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_394"), empty_list);
symInfo = listCons(stringValue("Function fn_394"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("filter"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_397"), empty_list);
symInfo = listCons(stringValue("Function fn_397"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_402"), empty_list);
symInfo = listCons(stringValue("Function fn_402"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_405"), empty_list);
symInfo = listCons(stringValue("Function fn_405"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_741"), empty_list);
symInfo = listCons(stringValue("Function fn_741"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_669"), empty_list);
symInfo = listCons(stringValue("Function fn_669"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_673"), empty_list);
symInfo = listCons(stringValue("Function fn_673"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_441"), empty_list);
symInfo = listCons(stringValue("Function fn_441"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_737"), empty_list);
symInfo = listCons(stringValue("Function fn_737"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_422"), empty_list);
symInfo = listCons(stringValue("Function fn_422"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_426"), empty_list);
symInfo = listCons(stringValue("Function fn_426"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("any?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_430"), empty_list);
symInfo = listCons(stringValue("Function protoFn_430"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_434"), empty_list);
symInfo = listCons(stringValue("Value *var_434"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ZipList"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_633"), empty_list);
symInfo = listCons(stringValue("Function fn_633"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_745"), empty_list);
symInfo = listCons(stringValue("Function fn_745"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_447"), empty_list);
symInfo = listCons(stringValue("Function fn_447"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_454"), empty_list);
symInfo = listCons(stringValue("Function fn_454"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partial"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_469"), empty_list);
symInfo = listCons(stringValue("Function fn_469"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-concat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_472"), empty_list);
symInfo = listCons(stringValue("Function fn_472"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_477"), empty_list);
symInfo = listCons(stringValue("Function fn_477"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_481"), empty_list);
symInfo = listCons(stringValue("Function fn_481"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_661"), empty_list);
symInfo = listCons(stringValue("Function fn_661"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_561"), empty_list);
symInfo = listCons(stringValue("Function fn_561"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_565"), empty_list);
symInfo = listCons(stringValue("Function fn_565"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_665"), empty_list);
symInfo = listCons(stringValue("Function fn_665"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_495"), empty_list);
symInfo = listCons(stringValue("Function fn_495"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_639"), empty_list);
symInfo = listCons(stringValue("Function fn_639"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_643"), empty_list);
symInfo = listCons(stringValue("Function fn_643"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_647"), empty_list);
symInfo = listCons(stringValue("Function fn_647"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_507"), empty_list);
symInfo = listCons(stringValue("Function fn_507"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_509"), empty_list);
symInfo = listCons(stringValue("Function fn_509"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_511"), empty_list);
symInfo = listCons(stringValue("Function fn_511"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_513"), empty_list);
symInfo = listCons(stringValue("Function fn_513"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("some"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_516"), empty_list);
symInfo = listCons(stringValue("Function fn_516"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("inc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_519"), empty_list);
symInfo = listCons(stringValue("Function fn_519"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_522"), empty_list);
symInfo = listCons(stringValue("Function fn_522"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_525"), empty_list);
symInfo = listCons(stringValue("Function fn_525"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_528"), empty_list);
symInfo = listCons(stringValue("Function fn_528"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("-"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_579"), empty_list);
symInfo = listCons(stringValue("Function fn_579"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_586"), empty_list);
symInfo = listCons(stringValue("Function fn_586"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_589"), empty_list);
symInfo = listCons(stringValue("Function fn_589"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("drop"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_592"), empty_list);
symInfo = listCons(stringValue("Function fn_592"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_596"), empty_list);
symInfo = listCons(stringValue("Function fn_596"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("replace-at-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_599"), empty_list);
symInfo = listCons(stringValue("Function fn_599"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_602"), empty_list);
symInfo = listCons(stringValue("Function fn_602"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_605"), empty_list);
symInfo = listCons(stringValue("Function fn_605"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition-all"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_608"), empty_list);
symInfo = listCons(stringValue("Function fn_608"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_612"), empty_list);
symInfo = listCons(stringValue("Function fn_612"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("last"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_615"), empty_list);
symInfo = listCons(stringValue("Function fn_615"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_618"), empty_list);
symInfo = listCons(stringValue("Function fn_618"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_621"), empty_list);
symInfo = listCons(stringValue("Function fn_621"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_624"), empty_list);
symInfo = listCons(stringValue("Function fn_624"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_628"), empty_list);
symInfo = listCons(stringValue("Function protoFn_628"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_632"), empty_list);
symInfo = listCons(stringValue("Value *var_632"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("HashMap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_681"), empty_list);
symInfo = listCons(stringValue("Function fn_681"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_685"), empty_list);
symInfo = listCons(stringValue("Function fn_685"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_689"), empty_list);
symInfo = listCons(stringValue("Function fn_689"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_693"), empty_list);
symInfo = listCons(stringValue("Function fn_693"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_697"), empty_list);
symInfo = listCons(stringValue("Function fn_697"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_704"), empty_list);
symInfo = listCons(stringValue("Function fn_704"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_707"), empty_list);
symInfo = listCons(stringValue("Function fn_707"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_714"), empty_list);
symInfo = listCons(stringValue("Function fn_714"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_717"), empty_list);
symInfo = listCons(stringValue("Function fn_717"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_720"), empty_list);
symInfo = listCons(stringValue("Function fn_720"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_727"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_727"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-found"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_739"), empty_list);
symInfo = listCons(stringValue("Function fn_739"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_747"), empty_list);
symInfo = listCons(stringValue("Function fn_747"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_750"), empty_list);
symInfo = listCons(stringValue("Function fn_750"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_753"), empty_list);
symInfo = listCons(stringValue("Function fn_753"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_756"), empty_list);
symInfo = listCons(stringValue("Function fn_756"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_759"), empty_list);
symInfo = listCons(stringValue("Function fn_759"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_762"), empty_list);
symInfo = listCons(stringValue("Function fn_762"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_765"), empty_list);
symInfo = listCons(stringValue("Function fn_765"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_768"), empty_list);
symInfo = listCons(stringValue("Function fn_768"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("repeat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
return((Value *)defSyms);
}

Value *types() {
List *types = empty_list;
List *typeInfo;
typeInfo = listCons(numberValue(1), empty_list);
typeInfo = listCons(symbolValue("String"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(2), empty_list);
typeInfo = listCons(symbolValue("Number"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(3), empty_list);
typeInfo = listCons(symbolValue("Function"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(4), empty_list);
typeInfo = listCons(symbolValue("List"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(5), empty_list);
typeInfo = listCons(symbolValue("Keyword"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(6), empty_list);
typeInfo = listCons(symbolValue("SubStr"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(7), empty_list);
typeInfo = listCons(symbolValue("Symbol"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(8), empty_list);
typeInfo = listCons(symbolValue("FnArity"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(9), empty_list);
typeInfo = listCons(symbolValue("9"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(10), empty_list);
typeInfo = listCons(symbolValue("ZipList"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(11), empty_list);
typeInfo = listCons(symbolValue("11"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(12), empty_list);
typeInfo = listCons(symbolValue("HashMap"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(13), empty_list);
typeInfo = listCons(symbolValue("13"), typeInfo);
types = listCons((Value *)typeInfo, types);
return((Value *)types);
}


Value *counts() {
List *cnts = empty_list;
cnts = listCons(numberValue(810), cnts);
return((Value *)cnts);
}

