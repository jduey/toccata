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
typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;
List *listCons(Value *x, List *l);
Value *stringValue(char *s);
const int64_t NumberType;
const int64_t KeywordType;
const int64_t SymbolType;
const int64_t StringType;
const int64_t SubStringType;
const int64_t ListType;
const int64_t FunctionType;
const int64_t OpaqueType;
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
const int64_t OpaqueType = 9;
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
  } else if (v->type == 9) {
    v->refs = -10;
    free_count++;
#ifdef REF_COUNT
    free(v);
#endif
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
Number _num_9 = {2, -1, 9};
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
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[65];} _str_16 = {1, -1, 64,"typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"};
Value *var_38 = (Value *)&trueVal;;
Value *var_39 = (Value *)&falseVal;;

// --------- output-to-file --------------
Function fn_40;
Value *arityImpl_41(List *closures, Value *arg0) {
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
Function fn_40 = {3, -1, "output-to-file", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_41}}};


// --------- standard-output --------------
Function fn_43;
Value *arityImpl_44(List *closures) {
outStream = stdout;
    return((Value *)&trueVal);
};


// --------- standard-output main body --------------
Function fn_43 = {3, -1, "standard-output", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_44}}};


// --------- symkey-name --------------
Function fn_46;
Value *arityImpl_47(List *closures, Value *arg0) {
return(stringValue(((SubString *)arg0)->buffer));
};


// --------- symkey-name main body --------------
Function fn_46 = {3, -1, "symkey-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_47}}};


// --------- char-code --------------
Function fn_49;
Value *arityImpl_50(List *closures, Value *arg0) {
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
Function fn_49 = {3, -1, "char-code", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_50}}};


// --------- symbol --------------
Function fn_52;
Value *arityImpl_53(List *closures, Value *arg0) {
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
                   } else if (arg0->type == SymbolType) {
                     return(arg0);
                   }
                     abort();
};


// --------- symbol main body --------------
Function fn_52 = {3, -1, "symbol", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_53}}};


// --------- new-keyword --------------
Function fn_55;
Value *arityImpl_56(List *closures, Value *arg0) {
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
Function fn_55 = {3, -1, "new-keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_56}}};


// --------- abort --------------
Function fn_58;
Value *arityImpl_59(List *closures) {
abort();
    return(true);
};


// --------- abort main body --------------
Function fn_58 = {3, -1, "abort", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_59}}};


// --------- get-type --------------
Function fn_61;
Value *arityImpl_62(List *closures, Value *arg0) {
return(numberValue(arg0->type));};


// --------- get-type main body --------------
Function fn_61 = {3, -1, "get-type", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_62}}};


// --------- type= --------------
Function fn_64;
Value *arityImpl_65(List *closures, Value *arg0, Value *arg1) {
if (arg0->type == arg1->type)
                   return(true);
                else
                   return(false);
};


// --------- type= main body --------------
Function fn_64 = {3, -1, "type=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_65}}};


// --------- subs --------------
Function fn_67;
Value *arityImpl_68(List *closures, Value *arg0, Value *arg1) {
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

Value *arityImpl_69(List *closures, Value *arg0, Value *arg1, Value *arg2) {
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
Function fn_67 = {3, -1, "subs", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_68}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_69}}};


// --------- number-str --------------
Function fn_71;
Value *arityImpl_72(List *closures, Value *arg0) {
String *numStr = (String *)my_malloc(sizeof(String) + 10);
    snprintf(numStr->buffer, 9, "%lld", ((Number *)arg0)->numVal);
    numStr->type = StringType;
    numStr->len = strlen(numStr->buffer);
    return((Value *)numStr);
};


// --------- number-str main body --------------
Function fn_71 = {3, -1, "number-str", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_72}}};


// --------- number= --------------
Function fn_74;
Value *arityImpl_75(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      return(false);
   } else if (((Number *)arg0)->numVal != ((Number *)arg1)->numVal)
      return(false);
   else
      return(true);
};


// --------- number= main body --------------
Function fn_74 = {3, -1, "number=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_75}}};


// --------- number-less-than --------------
Function fn_77;
Value *arityImpl_78(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'number-less-than'\n");
      abort();
   } else if (((Number *)arg0)->numVal < ((Number *)arg1)->numVal)
      return(true);
   else
      return(false);
};


// --------- number-less-than main body --------------
Function fn_77 = {3, -1, "number-less-than", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_78}}};


// --------- add-numbers --------------
Function fn_80;
Value *arityImpl_81(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'add-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal + ((Number *)arg1)->numVal));
};


// --------- add-numbers main body --------------
Function fn_80 = {3, -1, "add-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_81}}};


// --------- subtract-numbers --------------
Function fn_83;
Value *arityImpl_84(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'subtract-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal - ((Number *)arg1)->numVal));
};


// --------- subtract-numbers main body --------------
Function fn_83 = {3, -1, "subtract-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_84}}};


// --------- mult-numbers --------------
Function fn_86;
Value *arityImpl_87(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\n*** invalid types for 'mult-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal * ((Number *)arg1)->numVal));
};


// --------- mult-numbers main body --------------
Function fn_86 = {3, -1, "mult-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_87}}};


// --------- rem --------------
Function fn_89;
Value *arityImpl_90(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != NumberType ||
        arg1->type != NumberType) {
      fprintf(outStream, "\ninvalid types for 'rem'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal %
                         ((Number *)arg1)->numVal));
};


// --------- rem main body --------------
Function fn_89 = {3, -1, "rem", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_90}}};

Value *var_92 = (Value *)&(List){4,-1,0,0,0};;

// --------- cons --------------
Function fn_93;
Value *arityImpl_94(List *closures, Value *arg0) {
incRef(arg0);
return((Value *)listCons(arg0, empty_list));
};

Value *arityImpl_95(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
incRef(arg1);
return((Value *)listCons(arg0, (List *)arg1));
};


// --------- cons main body --------------
Function fn_93 = {3, -1, "cons", 2, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_94}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_95}}};


// --------- list-count --------------
Function fn_97;
Value *arityImpl_98(List *closures, Value *arg0) {
if (arg0->type != ListType)
      abort();
    else
      return(numberValue(((List *)arg0)->len));};


// --------- list-count main body --------------
Function fn_97 = {3, -1, "list-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_98}}};


// --------- car --------------
Function fn_100;
Value *arityImpl_101(List *closures, Value *arg0) {
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
Function fn_100 = {3, -1, "car", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_101}}};


// --------- cdr --------------
Function fn_103;
Value *arityImpl_104(List *closures, Value *arg0) {
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
Function fn_103 = {3, -1, "cdr", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_104}}};


// --------- fn-name --------------
Function fn_106;
Value *arityImpl_107(List *closures, Value *arg0) {
if (arg0->type != FunctionType) {
      fprintf(stderr, "\n*** invalid type for 'fn-name'\n");
      abort();
    } else
      return(stringValue(((Function *)arg0)->name));
};


// --------- fn-name main body --------------
Function fn_106 = {3, -1, "fn-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_107}}};


// --------- char --------------
Function fn_109;
Value *arityImpl_110(List *closures, Value *arg0) {
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
Function fn_109 = {3, -1, "char", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_110}}};


// --------- str-count --------------
Function fn_112;
Value *arityImpl_113(List *closures, Value *arg0) {
if (arg0->type != StringType && arg0->type != SubStringType ) {
      fprintf(outStream, "\ninvalid type for 'str-count'\n");
      abort();
    }
   return(numberValue(((String *)arg0)->len));
};


// --------- str-count main body --------------
Function fn_112 = {3, -1, "str-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_113}}};


// --------- str= --------------
Function fn_115;
Value *arityImpl_116(List *closures, Value *arg0, Value *arg1) {
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
Function fn_115 = {3, -1, "str=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_116}}};


// --------- symkey= --------------
Function fn_118;
Value *arityImpl_119(List *closures, Value *arg0, Value *arg1) {
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
Function fn_118 = {3, -1, "symkey=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_119}}};


// --------- str-malloc --------------
Function fn_121;
Value *arityImpl_122(List *closures, Value *arg0) {
String *strVal = (String *)my_malloc(sizeof(String) + ((Number *)arg0)->numVal);
    strVal->type = StringType;
    strVal->len = 0;
    strVal->buffer[0] = 0;
    return((Value *)strVal);
};


// --------- str-malloc main body --------------
Function fn_121 = {3, -1, "str-malloc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_122}}};


// --------- str-append --------------
Function fn_124;
Value *arityImpl_125(List *closures, Value *arg0, Value *arg1) {
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
Function fn_124 = {3, -1, "str-append", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_125}}};


// --------- pr-err* --------------
Function fn_127;
Value *arityImpl_128(List *closures, Value *arg0) {
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
Function fn_127 = {3, -1, "pr-err*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_128}}};


// --------- slurp --------------
Function fn_130;
Value *arityImpl_131(List *closures, Value *arg0) {
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
Function fn_130 = {3, -1, "slurp", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_131}}};


// --------- fn-apply --------------
Function fn_133;
Value *arityImpl_134(List *closures, Value *arg0, Value *arg1) {
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
Function fn_133 = {3, -1, "fn-apply", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_134}}};


// --------- escape-chars --------------
Function fn_136;
Value *arityImpl_137(List *closures, Value *arg0) {
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
Function fn_136 = {3, -1, "escape-chars", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_137}}};


// --------- pr* --------------
Function fn_139;
Value *arityImpl_140(List *closures, Value *arg0) {
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
Function fn_139 = {3, -1, "pr*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_140}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[16];} _str_17 = {1, -1, 15,":match*-one-arg"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[17];} _str_18 = {1, -1, 16,":match*-two-args"};
ProtoImpls *protoImpls_142;
Value *protoFnImpl_145(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_142);
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
FnArity protoFnArity_146 = {8, -1, 1, (List *)0, 0, protoFnImpl_145};
Function protoFn_143 = {3, -1, "bippity", 1, {&protoFnArity_146}};

ProtoImpls *protoImpls_147;
Value *arityImpl_150(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_140(empty_list, (Value *)&_str_17);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *protoFnImpl_151(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_147);
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
FnArity protoFnArity_152 = {8, -1, 1, (List *)0, 0, protoFnImpl_151};
Value *protoFnImpl_153(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_147);
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
FnArity protoFnArity_154 = {8, -1, 2, (List *)0, 0, protoFnImpl_153};
Function defaultFn_149 = {3, -1, "match*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_150}}};

Function protoFn_148 = {3, -1, "match*", 2, {&protoFnArity_152,
&protoFnArity_154}};

ProtoImpls *protoImpls_155;
Value *protoFnImpl_158(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_155);
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
FnArity protoFnArity_159 = {8, -1, 2, (List *)0, 0, protoFnImpl_158};
Function protoFn_156 = {3, -1, "instance?", 1, {&protoFnArity_159}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[31];} _str_19 = {1, -1, 30,"*** 'flat-map' not implemented"};
ProtoImpls *protoImpls_160;
Value *arityImpl_163(List *closures, Value *arg0, Value *arg1) {
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
Value *rslt4 = arityImpl_59(empty_list);
incRef(rslt4);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};

Value *protoFnImpl_164(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_160);
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
FnArity protoFnArity_165 = {8, -1, 2, (List *)0, 0, protoFnImpl_164};
Function defaultFn_162 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_163}}};

Function protoFn_161 = {3, -1, "flat-map", 1, {&protoFnArity_165}};

ProtoImpls *protoImpls_166;

// --------- anon --------------
Function fn_170;
Value *arityImpl_171(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- anon main body --------------
Function fn_170 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_171}}};

Value *arityImpl_169(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_164(empty_list, arg0, (Value *)&fn_170);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_172(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_166);
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
FnArity protoFnArity_173 = {8, -1, 1, (List *)0, 0, protoFnImpl_172};
Function defaultFn_168 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_169}}};

Function protoFn_167 = {3, -1, "flatten", 1, {&protoFnArity_173}};

ProtoImpls *protoImpls_174;
Value *protoFnImpl_177(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_174);
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
FnArity protoFnArity_178 = {8, -1, 1, (List *)0, 0, protoFnImpl_177};
Function protoFn_175 = {3, -1, "extract", 1, {&protoFnArity_178}};

ProtoImpls *protoImpls_179;
Value *protoFnImpl_182(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_179);
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
FnArity protoFnArity_183 = {8, -1, 2, (List *)0, 0, protoFnImpl_182};
Function protoFn_180 = {3, -1, "extend", 1, {&protoFnArity_183}};

ProtoImpls *protoImpls_184;
Value *protoFnImpl_187(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_184);
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
FnArity protoFnArity_188 = {8, -1, 1, (List *)0, 0, protoFnImpl_187};
Function protoFn_185 = {3, -1, "duplicate", 1, {&protoFnArity_188}};

// forward declaration for 'comprehend'
Value *var_189;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_20 = {1, -1, 26,"*** 'wrap' not implemented"};
Number _num_10 = {2, -1, 0};
ProtoImpls *protoImpls_190;
Value *arityImpl_193(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_19)->type != 3) {
rslt3 = protoFnImpl_5(empty_list, var_19, (Value *)&_str_20);
} else {
FnArity *arity0 = findFnArity(var_19, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_20);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef((Value *)&_str_20);
varArgs1 = (List *)listCons((Value *)&_str_20, varArgs1);
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

Value *protoFnImpl_194(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_190);
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
FnArity protoFnArity_195 = {8, -1, 2, (List *)0, 0, protoFnImpl_194};
Function defaultFn_192 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_193}}};

Function protoFn_191 = {3, -1, "wrap", 1, {&protoFnArity_195}};

ProtoImpls *protoImpls_196;

// --------- anon --------------
Function fn_200;
Value *arityImpl_201(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((var_189)->type != 3) {
rslt4 = protoFnImpl_7(empty_list, var_189, arg0, val0);
} else {
FnArity *arity1 = findFnArity(var_189, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_189)->name);
  abort();
}
}
incRef(rslt4);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};


// --------- anon --------------
Function fn_202;
Value *arityImpl_203(List *closures, Value *arg0) {
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
Value *rslt5 = protoFnImpl_194(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_199(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_98(empty_list, arg1);
Value *rslt4 = arityImpl_75(empty_list, (Value *)&_num_10, rslt3);
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
arity_5->fn = arityImpl_203;
incRef((Value *)arg0);
arity_5->closures = listCons((Value *)arg0, (List *)arity_5->closures);
Function *fn_202 = malloc_function(1);
fn_202->type = 3;
fn_202->name = "anon";
fn_202->arityCount = 1;
fn_202->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_164(empty_list, arg0, (Value *)fn_202);
incRef(rslt6);
cond0 = rslt6;
decRef((Value *)fn_202);
my_free((Value *)fn_202);
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
arity_1->fn = arityImpl_201;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_200 = malloc_function(1);
fn_200->type = 3;
fn_200->name = "anon";
fn_200->arityCount = 1;
fn_200->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_164(empty_list, arg0, (Value *)fn_200);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_200);
my_free((Value *)fn_200);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoFnImpl_204(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_196);
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
FnArity protoFnArity_205 = {8, -1, 2, (List *)0, 0, protoFnImpl_204};
Function defaultFn_198 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_199}}};

Function protoFn_197 = {3, -1, "apply*", 1, {&protoFnArity_205}};


// --------- apply --------------
Function fn_206;
Value *arityImpl_207(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = protoFnImpl_204(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- apply main body --------------
Function fn_206 = {3, -1, "apply", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_207}}};


// --------- apply-to --------------
Function fn_209;
Value *arityImpl_210(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt4 = arityImpl_98(empty_list, arg1);
Value *rslt5 = arityImpl_75(empty_list, (Value *)&_num_10, rslt4);
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
Value *rslt1 = arityImpl_101(empty_list, arg1);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, arg0);
Value *rslt3 = protoFnImpl_204(empty_list, rslt2, arg1);
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
Function fn_209 = {3, -1, "apply-to", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_210}}};


// --------- list --------------
Function fn_212;
Value *arityImpl_213(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_212 = {3, -1, "list", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_213}}};

ProtoImpls *protoImpls_215;

// --------- anon --------------
Function fn_219;
Value *arityImpl_220(List *closures, Value *arg0) {
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
Value *rslt6 = protoFnImpl_194(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_218(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_220;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_219 = malloc_function(1);
fn_219->type = 3;
fn_219->name = "anon";
fn_219->arityCount = 1;
fn_219->arities[0] = arity_0;
Value *rslt1 = protoFnImpl_164(empty_list, arg0, (Value *)fn_219);
incRef(rslt1);
decRef((Value *)fn_219);
my_free((Value *)fn_219);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_221(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_215);
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
FnArity protoFnArity_222 = {8, -1, 2, (List *)0, 0, protoFnImpl_221};
Function defaultFn_217 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_218}}};

Function protoFn_216 = {3, -1, "map", 1, {&protoFnArity_222}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_21 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_223;
Value *arityImpl_226(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
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
Value *rslt5 = arityImpl_59(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_227(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_223);
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
FnArity protoFnArity_228 = {8, -1, 1, (List *)0, 0, protoFnImpl_227};
Function defaultFn_225 = {3, -1, "name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_226}}};

Function protoFn_224 = {3, -1, "name", 1, {&protoFnArity_228}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_22 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_229;
Value *arityImpl_232(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
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
Value *rslt5 = arityImpl_59(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_233(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_229);
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
FnArity protoFnArity_234 = {8, -1, 1, (List *)0, 0, protoFnImpl_233};
Function defaultFn_231 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_232}}};

Function protoFn_230 = {3, -1, "string-list", 1, {&protoFnArity_234}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_23 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_235;
Value *arityImpl_238(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
Value *rslt4;
if((var_19)->type != 3) {
rslt4 = protoFnImpl_7(empty_list, var_19, (Value *)&_str_23, rslt0);
} else {
FnArity *arity1 = findFnArity(var_19, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_23, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_23);
varArgs2 = (List *)listCons((Value *)&_str_23, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_19)->name);
  abort();
}
}
Value *rslt5 = arityImpl_59(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_239(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_235);
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
FnArity protoFnArity_240 = {8, -1, 1, (List *)0, 0, protoFnImpl_239};
Function defaultFn_237 = {3, -1, "serialize", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_238}}};

Function protoFn_236 = {3, -1, "serialize", 1, {&protoFnArity_240}};


// --------- list-empty? --------------
Function fn_241;
Value *arityImpl_242(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_98(empty_list, arg0);
Value *rslt1 = arityImpl_75(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- list-empty? main body --------------
Function fn_241 = {3, -1, "list-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_242}}};


// --------- interpose --------------
Function fn_244;

// --------- anon --------------
Function fn_246;
Value *arityImpl_247(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)val0);
varArgs1 = (List *)listCons((Value *)val0, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *arityImpl_245(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = arityImpl_242(empty_list, arg0);
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
Value *rslt1 = arityImpl_101(empty_list, arg0);
Value *rslt2 = arityImpl_104(empty_list, arg0);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_247;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_246 = malloc_function(1);
fn_246->type = 3;
fn_246->name = "anon";
fn_246->arityCount = 1;
fn_246->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_164(empty_list, rslt2, (Value *)fn_246);
Value *rslt5 = arityImpl_95(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_246);
my_free((Value *)fn_246);
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
Function fn_244 = {3, -1, "interpose", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_245}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_24 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_25 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_249;
Value *arityImpl_250(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = protoFnImpl_164(empty_list, arg0, (Value *)&protoFn_236);
Value *rslt1 = arityImpl_245(empty_list, rslt0, (Value *)&_str_24);
Value *rslt2 = protoFnImpl_221(empty_list, rslt1, (Value *)&fn_139);
Value *rslt3 = arityImpl_140(empty_list, (Value *)&_str_25);
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
Function fn_249 = {3, -1, "prn", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_250}}};


// --------- print --------------
Function fn_252;
Value *arityImpl_253(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_245(empty_list, arg0, (Value *)&_str_24);
Value *rslt1 = protoFnImpl_164(empty_list, rslt0, (Value *)&protoFn_230);
Value *rslt2 = protoFnImpl_221(empty_list, rslt1, (Value *)&fn_139);
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
Function fn_252 = {3, -1, "print", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_253}}};


// --------- println --------------
Function fn_255;
Value *arityImpl_256(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_245(empty_list, arg0, (Value *)&_str_24);
Value *rslt1 = protoFnImpl_164(empty_list, rslt0, (Value *)&protoFn_230);
Value *rslt2 = protoFnImpl_221(empty_list, rslt1, (Value *)&fn_139);
Value *rslt3 = arityImpl_140(empty_list, (Value *)&_str_25);
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
Function fn_255 = {3, -1, "println", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_256}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_26 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_258;
Value *arityImpl_259(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_128(empty_list, (Value *)&_str_26);
Value *rslt1 = arityImpl_245(empty_list, arg0, (Value *)&_str_24);
Value *rslt2 = protoFnImpl_164(empty_list, rslt1, (Value *)&protoFn_230);
Value *rslt3 = protoFnImpl_221(empty_list, rslt2, (Value *)&fn_127);
Value *rslt4 = arityImpl_128(empty_list, (Value *)&_str_25);
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
Function fn_258 = {3, -1, "print-err", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_259}}};

Value *var_19 = (Value *)&fn_258;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_27 = {1, -1, 21,"'=*' not implemented:"};
ProtoImpls *protoImpls_260;
Value *arityImpl_263(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_27);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_27, varArgs0);
Value *rslt1 = arityImpl_259(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_59(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_264(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_260);
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
FnArity protoFnArity_265 = {8, -1, 2, (List *)0, 0, protoFnImpl_264};
Function defaultFn_262 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_263}}};

Function protoFn_261 = {3, -1, "=*", 1, {&protoFnArity_265}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_28 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_266;
Value *arityImpl_269(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_28);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_28, varArgs0);
Value *rslt1 = arityImpl_259(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_59(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_270(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_266);
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
FnArity protoFnArity_271 = {8, -1, 2, (List *)0, 0, protoFnImpl_270};
Function defaultFn_268 = {3, -1, "<*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_269}}};

Function protoFn_267 = {3, -1, "<*", 1, {&protoFnArity_271}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_29 = {1, -1, 28,"'count' not implemented for "};
ProtoImpls *protoImpls_272;
Value *protoFnImpl_275(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_272);
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
FnArity protoFnArity_276 = {8, -1, 1, (List *)0, 0, protoFnImpl_275};
Function protoFn_273 = {3, -1, "empty?", 1, {&protoFnArity_276}};

ProtoImpls *protoImpls_277;
Value *protoFnImpl_280(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_277);
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
FnArity protoFnArity_281 = {8, -1, 1, (List *)0, 0, protoFnImpl_280};
Function protoFn_278 = {3, -1, "empty", 1, {&protoFnArity_281}};

ProtoImpls *protoImpls_282;
Value *protoFnImpl_285(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_282);
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
FnArity protoFnArity_286 = {8, -1, 2, (List *)0, 0, protoFnImpl_285};
Function protoFn_283 = {3, -1, "destruct", 1, {&protoFnArity_286}};

ProtoImpls *protoImpls_287;
Value *arityImpl_290(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_29);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_29, varArgs0);
Value *rslt1 = arityImpl_259(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_59(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_291(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_287);
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
FnArity protoFnArity_292 = {8, -1, 1, (List *)0, 0, protoFnImpl_291};
Function defaultFn_289 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_290}}};

Function protoFn_288 = {3, -1, "count", 1, {&protoFnArity_292}};

ProtoImpls *protoImpls_293;
Value *protoFnImpl_296(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_293);
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
FnArity protoFnArity_297 = {8, -1, 2, (List *)0, 0, protoFnImpl_296};
Function protoFn_294 = {3, -1, "conj", 1, {&protoFnArity_297}};


// --------- not-empty? --------------
Function fn_298;
Value *arityImpl_299(List *closures, Value *arg0) {
Value *cond0;
Value *rslt1 = protoFnImpl_275(empty_list, arg0);
decRef(rslt1);
my_free(rslt1);

if (isTrue(rslt1)) {
decRef(rslt1);
my_free(rslt1);
incRef(var_39);
cond0 = var_39;
} else {
decRef(rslt1);
my_free(rslt1);
incRef(var_38);
cond0 = var_38;
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- not-empty? main body --------------
Function fn_298 = {3, -1, "not-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_299}}};

ProtoImpls *protoImpls_301;
Value *arityImpl_304(List *closures, Value *arg0) {
incRef(var_39);
return(var_39);
};

Value *protoFnImpl_305(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_301);
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
FnArity protoFnArity_306 = {8, -1, 1, (List *)0, 0, protoFnImpl_305};
Function defaultFn_303 = {3, -1, "seq?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_304}}};

Function protoFn_302 = {3, -1, "seq?", 1, {&protoFnArity_306}};

ProtoImpls *protoImpls_307;
Value *protoFnImpl_310(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_307);
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
FnArity protoFnArity_311 = {8, -1, 1, (List *)0, 0, protoFnImpl_310};
Function protoFn_308 = {3, -1, "seq", 1, {&protoFnArity_311}};

ProtoImpls *protoImpls_312;
Value *protoFnImpl_315(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_312);
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
FnArity protoFnArity_316 = {8, -1, 1, (List *)0, 0, protoFnImpl_315};
Function protoFn_313 = {3, -1, "first", 1, {&protoFnArity_316}};

ProtoImpls *protoImpls_317;
Value *protoFnImpl_320(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_317);
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
FnArity protoFnArity_321 = {8, -1, 1, (List *)0, 0, protoFnImpl_320};
Function protoFn_318 = {3, -1, "rest", 1, {&protoFnArity_321}};


// --------- second --------------
Function fn_322;
Value *arityImpl_323(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_320(empty_list, arg0);
Value *rslt1 = protoFnImpl_315(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- second main body --------------
Function fn_322 = {3, -1, "second", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_323}}};

ProtoImpls *protoImpls_325;
Value *protoFnImpl_328(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_325);
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
FnArity protoFnArity_329 = {8, -1, 2, (List *)0, 0, protoFnImpl_328};
Function protoFn_326 = {3, -1, "traverse", 1, {&protoFnArity_329}};

ProtoImpls *protoImpls_330;
Value *protoFnImpl_333(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_330);
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
FnArity protoFnArity_334 = {8, -1, 2, (List *)0, 0, protoFnImpl_333};
Function protoFn_331 = {3, -1, "crush", 1, {&protoFnArity_334}};

ProtoImpls *protoImpls_335;
Value *protoFnImpl_338(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_335);
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
FnArity protoFnArity_339 = {8, -1, 1, (List *)0, 0, protoFnImpl_338};
Function protoFn_336 = {3, -1, "zero", 1, {&protoFnArity_339}};

ProtoImpls *protoImpls_340;
Value *protoFnImpl_343(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_340);
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
FnArity protoFnArity_344 = {8, -1, 2, (List *)0, 0, protoFnImpl_343};
Function protoFn_341 = {3, -1, "comp*", 1, {&protoFnArity_344}};


// --------- comp --------------
Function fn_345;
Value *arityImpl_346(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_343(empty_list, arg0, arg1);
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
Function fn_345 = {3, -1, "comp", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_346}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[24];} _str_30 = {1, -1, 23,"'get' not implemented: "};
SubString _kw_0 = {5, -1, 2, 0, ":m"};
SubString _kw_1 = {5, -1, 2, 0, ":k"};
ProtoImpls *protoImpls_348;
Value *protoFnImpl_351(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_348);
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
FnArity protoFnArity_352 = {8, -1, 3, (List *)0, 0, protoFnImpl_351};
Function protoFn_349 = {3, -1, "assoc", 1, {&protoFnArity_352}};

ProtoImpls *protoImpls_353;
Value *arityImpl_356(List *closures, Value *arg0, Value *arg1, Value *arg2) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)(Value *)&_kw_1);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_kw_0);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_0, varArgs0);
incRef((Value *)(Value *)&_str_30);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_30, varArgs0);
Value *rslt1 = arityImpl_259(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_59(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_357(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_353);
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
FnArity protoFnArity_358 = {8, -1, 3, (List *)0, 0, protoFnImpl_357};
Function defaultFn_355 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_356}}};

Function protoFn_354 = {3, -1, "get", 1, {&protoFnArity_358}};

ProtoImpls *protoImpls_359;
Value *protoFnImpl_362(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_359);
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
FnArity protoFnArity_363 = {8, -1, 1, (List *)0, 0, protoFnImpl_362};
Function protoFn_360 = {3, -1, "keys", 1, {&protoFnArity_363}};

ProtoImpls *protoImpls_364;
Value *protoFnImpl_367(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_364);
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
FnArity protoFnArity_368 = {8, -1, 1, (List *)0, 0, protoFnImpl_367};
Function protoFn_365 = {3, -1, "vals", 1, {&protoFnArity_368}};


// --------- not --------------
Function fn_369;
Value *arityImpl_370(List *closures, Value *arg0) {
Value *cond0;

if (isTrue(arg0)) {
decRef(arg0);
my_free(arg0);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
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
Function fn_369 = {3, -1, "not", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_370}}};


// --------- and --------------
Function fn_372;
Value *arityImpl_373(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt1 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt2 = protoFnImpl_315(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = protoFnImpl_320(empty_list, arg0);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_372);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_372, varArgs4);
Value *rslt5 = arityImpl_207(empty_list, (Value *)varArgs4);
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
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- and main body --------------
Function fn_372 = {3, -1, "and", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_373}}};


// --------- or --------------
Function fn_375;
Value *arityImpl_376(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt4 = protoFnImpl_275(empty_list, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt5 = protoFnImpl_315(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_320(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)(Value *)&fn_375);
varArgs2 = (List *)listCons((Value *)(Value *)&fn_375, varArgs2);
Value *rslt3 = arityImpl_207(empty_list, (Value *)varArgs2);
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
Function fn_375 = {3, -1, "or", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_376}}};


// --------- = --------------
Function fn_378;
Value *arityImpl_379(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_264(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_380(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_315(empty_list, arg1);
Value *rslt5 = protoFnImpl_264(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_370(empty_list, rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_291(empty_list, arg1);
Value *rslt8 = arityImpl_75(empty_list, (Value *)&_num_1, rslt7);
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
incRef((Value *)(Value *)&fn_378);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_378, varArgs1);
Value *rslt2 = arityImpl_207(empty_list, (Value *)varArgs1);
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
Function fn_378 = {3, -1, "=", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_379}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_380}}};


// --------- < --------------
Function fn_382;
Value *arityImpl_383(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_270(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_384(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_315(empty_list, arg1);
Value *rslt5 = protoFnImpl_270(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_370(empty_list, rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_291(empty_list, arg1);
Value *rslt8 = arityImpl_75(empty_list, (Value *)&_num_1, rslt7);
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
incRef((Value *)(Value *)&fn_382);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_382, varArgs1);
Value *rslt2 = arityImpl_207(empty_list, (Value *)varArgs1);
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
Function fn_382 = {3, -1, "<", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_383}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_384}}};


// --------- list** --------------
Function fn_386;
Value *arityImpl_387(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg1);
Value *rslt2 = protoFnImpl_320(empty_list, arg1);
Value *rslt3 = arityImpl_387(closures, rslt1, rslt2);
Value *rslt4 = arityImpl_95(empty_list, arg0, rslt3);
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
Function fn_386 = {3, -1, "list**", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_387}}};


// --------- list* --------------
Function fn_389;
Value *arityImpl_390(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = arityImpl_387(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- list* main body --------------
Function fn_389 = {3, -1, "list*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_390}}};


// --------- reduce --------------
Function fn_392;
Value *arityImpl_393(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt10 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg0);
Value *rslt2 = protoFnImpl_320(empty_list, arg0);
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
Value *rslt9 = protoFnImpl_275(empty_list, rslt2);
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
Value *rslt8 = arityImpl_393(closures, rslt2, rslt6, arg2);
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
Function fn_392 = {3, -1, "reduce", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_393}}};


// --------- filter --------------
Function fn_395;
Value *arityImpl_396(List *closures, Value *arg0, Value *arg1) {
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
Function fn_395 = {3, -1, "filter", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_396}}};


// --------- remove --------------
Function fn_398;

// --------- anon --------------
Function fn_400;
Value *arityImpl_401(List *closures, Value *arg0) {
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
Value *rslt5 = arityImpl_370(empty_list, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_399(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_401;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_400 = malloc_function(1);
fn_400->type = 3;
fn_400->name = "anon";
fn_400->arityCount = 1;
fn_400->arities[0] = arity_0;
Value *rslt1 = arityImpl_396(empty_list, arg0, (Value *)fn_400);
incRef(rslt1);
decRef((Value *)fn_400);
my_free((Value *)fn_400);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- remove main body --------------
Function fn_398 = {3, -1, "remove", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_399}}};


// --------- reverse --------------
Function fn_403;
Value *arityImpl_404(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_280(empty_list, arg0);
Value *rslt1 = arityImpl_393(empty_list, arg0, rslt0, (Value *)&protoFn_294);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- reverse main body --------------
Function fn_403 = {3, -1, "reverse", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_404}}};


// --------- identity --------------
Function fn_406;
Value *arityImpl_407(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_406 = {3, -1, "identity", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_407}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_31 = {1, -1, 5,"<Fn: "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_32 = {1, -1, 1,">"};

// --------- string-list_impl --------------
Function fn_409;
Value *arityImpl_410(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_107(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_32);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_32, varArgs1);
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
incRef((Value *)(Value *)&_str_31);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_31, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
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
Function fn_409 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_410}}};


// --------- zero_impl --------------
Function fn_411;
Value *arityImpl_412(List *closures, Value *arg0) {
incRef((Value *)&fn_406);
return((Value *)&fn_406);
};


// --------- zero_impl main body --------------
Function fn_411 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_412}}};


// --------- comp*_impl --------------
Function fn_413;

// --------- anon --------------
Function fn_415;

// --------- anon --------------
Function fn_417;
Value *arityImpl_418(List *closures, Value *arg0, Value *arg1) {
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
Function fn_417 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_418}}};

Value *arityImpl_416(List *closures, Value *varArgs) {
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
Value *rslt3 = arityImpl_207(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
Value *rslt5 = arityImpl_393(empty_list, val0, rslt3, (Value *)&fn_417);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_414(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_416;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_415 = malloc_function(1);
fn_415->type = 3;
fn_415->name = "anon";
fn_415->arityCount = 1;
fn_415->arities[0] = arity_0;
incRef((Value *)fn_415);
decRef((Value *)fn_415);
my_free((Value *)fn_415);
return((Value *)fn_415);
};


// --------- comp*_impl main body --------------
Function fn_413 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_414}}};


// --------- apply*_impl --------------
Function fn_419;
Value *arityImpl_420(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg1);
Value *rslt2 = protoFnImpl_320(empty_list, arg1);
Value *rslt3 = arityImpl_387(empty_list, rslt1, rslt2);
Value *rslt4 = arityImpl_134(empty_list, arg0, rslt3);
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
Function fn_419 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_420}}};


// --------- =*_impl --------------
Function fn_421;
Value *arityImpl_422(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_75(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_421 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_422}}};


// --------- <*_impl --------------
Function fn_423;
Value *arityImpl_424(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_78(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- <*_impl main body --------------
Function fn_423 = {3, -1, "<*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_424}}};


// --------- string-list_impl --------------
Function fn_425;
Value *arityImpl_426(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_72(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
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
Function fn_425 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_426}}};


// --------- any? --------------
Function fn_427;
Value *arityImpl_428(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg1);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_315(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_320(empty_list, arg1);
Value *rslt2 = arityImpl_428(closures, arg0, rslt1);
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
Function fn_427 = {3, -1, "any?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_428}}};

ProtoImpls *protoImpls_430;
Value *protoFnImpl_433(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_430);
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
FnArity protoFnArity_434 = {8, -1, 1, (List *)0, 0, protoFnImpl_433};
Function protoFn_431 = {3, -1, ".v", 1, {&protoFnArity_434}};

// forward declaration for 'ZipList'
Value *var_435;

Number _num_11 = {2, -1, 11};
SubString _kw_2 = {5, -1, 4, 0, ":nil"};

// --------- instance?_impl --------------
Function fn_436;
Value *arityImpl_437(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_62(empty_list, arg1);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_11, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_436 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_437}}};

Value *protoImpl_438(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_439 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_438}}};


// --------- invoke_impl --------------
Function fn_440;

// --------- apply*_impl --------------
Function fn_442;

// --------- anon --------------
Function fn_444;
Value *arityImpl_445(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg0);
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
Function fn_444 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_445}}};

Value *arityImpl_443(List *closures, Value *arg0, Value *arg1) {
Value *val4 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt9 = arityImpl_428(empty_list, (Value *)&protoFn_273, arg1);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt2 = protoFnImpl_221(empty_list, arg1, (Value *)&fn_444);
Value *rslt3 = protoFnImpl_221(empty_list, arg1, (Value *)&protoFn_318);
List *varArgs5 = empty_list;
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
incRef((Value *)val4);
varArgs5 = (List *)listCons((Value *)val4, varArgs5);
Value *rslt6 = arityImpl_207(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_204(empty_list, arg0, rslt3);
Value *rslt8 = arityImpl_95(empty_list, rslt6, rslt7);
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

Value *protoImpl_446(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_447 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_446}}};


// --------- .v_impl --------------
Function fn_448;
Value *arityImpl_449(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_450(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_451 = {3, -1, ".v", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_450}}};

Value *arityImpl_441(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_443;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_442 = malloc_function(1);
fn_442->type = 3;
fn_442->name = "apply*_impl";
fn_442->arityCount = 1;
fn_442->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_449;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_448 = malloc_function(1);
fn_448->type = 3;
fn_448->name = ".v_impl";
fn_448->arityCount = 1;
fn_448->arities[0] = arity_1;
Value *reified_2 = (Value *)malloc_reified(2);
((ReifiedVal *)reified_2)->type = 11;
((ReifiedVal *)reified_2)->implCount = 2;
((ReifiedVal *)reified_2)->impls[0] = (Value *)fn_442;
incRef((Value *)fn_442);
((ReifiedVal *)reified_2)->impls[1] = (Value *)fn_448;
incRef((Value *)fn_448);
incRef(reified_2);
decRef((Value *)fn_442);
my_free((Value *)fn_442);
decRef((Value *)fn_448);
my_free((Value *)fn_448);
decRef(reified_2);
my_free(reified_2);
return(reified_2);
};


// --------- invoke_impl main body --------------
Function fn_440 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_441}}};

Value *protoImpl_452(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_453 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_452}}};

ReifiedVal reified_454 = {10, -1, 2, {(Value *)&fn_436, (Value *)&fn_440}};
Value *var_435 = (Value *)&reified_454;

// --------- partial --------------
Function fn_455;

// --------- anon --------------
Function fn_457;
Value *arityImpl_458(List *closures, Value *varArgs) {
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
Value *rslt3 = arityImpl_346(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val0);
varArgs4 = (List *)listCons((Value *)val0, varArgs4);
Value *rslt5 = arityImpl_207(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_456(List *closures, Value *varArgs) {
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
arity_0->fn = arityImpl_458;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_457 = malloc_function(1);
fn_457->type = 3;
fn_457->name = "anon";
fn_457->arityCount = 1;
fn_457->arities[0] = arity_0;
incRef((Value *)fn_457);
decRef((Value *)fn_457);
my_free((Value *)fn_457);
return((Value *)fn_457);
};

// --------- partial main body --------------
Function fn_455 = {3, -1, "partial", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_456}}};


// --------- comprehend --------------
Function fn_460;

// --------- anon --------------
Function fn_462;
Value *arityImpl_463(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_95(empty_list, arg1, arg0);
Value *rslt3 = arityImpl_404(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val1);
varArgs4 = (List *)listCons((Value *)val1, varArgs4);
Value *rslt5 = arityImpl_207(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = protoFnImpl_194(empty_list, val0, rslt5);
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
Function fn_464;

// --------- anon --------------
Function fn_466;
Value *arityImpl_467(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_95(empty_list, arg1, arg0);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)val1);
varArgs3 = (List *)listCons((Value *)val1, varArgs3);
Value *rslt4 = arityImpl_456(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_164(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_465(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_467;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_466 = malloc_function(1);
fn_466->type = 3;
fn_466->name = "anon";
fn_466->arityCount = 1;
fn_466->arities[0] = arity_0;
incRef((Value *)fn_466);
decRef((Value *)fn_466);
my_free((Value *)fn_466);
return((Value *)fn_466);
};


// --------- anon main body --------------
Function fn_464 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_465}}};


// --------- anon --------------
Function fn_468;
Value *arityImpl_469(List *closures, Value *arg0) {
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
Value *rslt6 = protoFnImpl_194(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_461(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt16 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg1);
Value *rslt2 = protoFnImpl_320(empty_list, arg1);
Value *rslt3 = arityImpl_404(empty_list, rslt2);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_463;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
incRef((Value *)rslt1);
arity_4->closures = listCons((Value *)rslt1, (List *)arity_4->closures);
Function *fn_462 = malloc_function(1);
fn_462->type = 3;
fn_462->name = "anon";
fn_462->arityCount = 1;
fn_462->arities[0] = arity_4;
Value *rslt6 = arityImpl_393(empty_list, rslt3, (Value *)fn_462, (Value *)&fn_464);
Value *cond7;
Value *rslt11 = protoFnImpl_291(empty_list, arg1);
Value *rslt12 = arityImpl_75(empty_list, (Value *)&_num_1, rslt11);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
Value *rslt13 = protoFnImpl_315(empty_list, arg1);
FnArity *arity_14 = malloc_fnArity();
arity_14->type = 8;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_469;
incRef((Value *)arg0);
arity_14->closures = listCons((Value *)arg0, (List *)arity_14->closures);
incRef((Value *)rslt1);
arity_14->closures = listCons((Value *)rslt1, (List *)arity_14->closures);
Function *fn_468 = malloc_function(1);
fn_468->type = 3;
fn_468->name = "anon";
fn_468->arityCount = 1;
fn_468->arities[0] = arity_14;
Value *rslt15 = protoFnImpl_164(empty_list, rslt13, (Value *)fn_468);
incRef(rslt15);
cond7 = rslt15;
decRef(rslt13);
my_free(rslt13);
decRef((Value *)fn_468);
my_free((Value *)fn_468);
decRef(rslt15);
my_free(rslt15);
} else {
decRef(rslt12);
my_free(rslt12);
List *varArgs8 = empty_list;
incRef((Value *)var_92);
varArgs8 = (List *)listCons((Value *)var_92, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_456(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_164(empty_list, rslt1, rslt9);
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
decRef((Value *)fn_462);
my_free((Value *)fn_462);
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
Function fn_460 = {3, -1, "comprehend", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_461}}};

Value *var_189 = (Value *)&fn_460;

// --------- list-concat --------------
Function fn_470;
Value *arityImpl_471(List *closures, Value *arg0) {
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
Function fn_470 = {3, -1, "list-concat", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_471}}};


// --------- list=* --------------
Function fn_473;

// --------- anon --------------
Function fn_475;
Value *arityImpl_476(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_315(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- anon main body --------------
Function fn_475 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_476}}};

Value *arityImpl_474(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt4 = protoFnImpl_315(empty_list, arg0);
Value *rslt5 = protoFnImpl_275(empty_list, rslt4);
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
Value *rslt7 = protoFnImpl_221(empty_list, arg0, (Value *)&fn_475);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)(Value *)&fn_378);
varArgs8 = (List *)listCons((Value *)(Value *)&fn_378, varArgs8);
Value *rslt9 = arityImpl_207(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = arityImpl_370(empty_list, rslt9);
decRef(rslt7);
my_free(rslt7);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_221(empty_list, arg0, (Value *)&protoFn_318);
Value *rslt2 = arityImpl_474(closures, rslt1);
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
Function fn_473 = {3, -1, "list=*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_474}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_33 = {1, -1, 1,"("};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_34 = {1, -1, 2,", "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_35 = {1, -1, 1,")"};

// --------- crush_impl --------------
Function fn_478;

// --------- anon --------------
Function fn_480;
Value *arityImpl_481(List *closures, Value *arg0, Value *arg1) {
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
Value *rslt6 = arityImpl_346(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
decRef(rslt4);
my_free(rslt4);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_479(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_104(empty_list, arg0);
Value *rslt1 = arityImpl_101(empty_list, arg0);
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
arity_6->fn = arityImpl_481;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_480 = malloc_function(1);
fn_480->type = 3;
fn_480->name = "anon";
fn_480->arityCount = 1;
fn_480->arities[0] = arity_6;
Value *rslt7 = arityImpl_393(empty_list, rslt0, rslt5, (Value *)fn_480);
incRef(rslt7);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
decRef((Value *)fn_480);
my_free((Value *)fn_480);
decRef(rslt7);
my_free(rslt7);
return(rslt7);
};


// --------- crush_impl main body --------------
Function fn_478 = {3, -1, "crush_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_479}}};


// --------- traverse_impl --------------
Function fn_482;
Value *arityImpl_483(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_221(empty_list, arg0, arg1);
Value *rslt1 = protoFnImpl_315(empty_list, rslt0);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, (Value *)&fn_212);
Value *rslt3 = protoFnImpl_204(empty_list, rslt2, rslt0);
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
Function fn_482 = {3, -1, "traverse_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_483}}};


// --------- =*_impl --------------
Function fn_484;
Value *arityImpl_485(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_62(empty_list, arg0);
Value *rslt5 = arityImpl_62(empty_list, arg1);
Value *rslt6 = arityImpl_379(empty_list, rslt4, rslt5);
Value *rslt7 = arityImpl_370(empty_list, rslt6);
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
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt8 = protoFnImpl_291(empty_list, arg0);
Value *rslt9 = protoFnImpl_291(empty_list, arg1);
Value *rslt10 = arityImpl_75(empty_list, rslt8, rslt9);
Value *rslt11 = arityImpl_370(empty_list, rslt10);
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
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt11);
my_free(rslt11);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_474(empty_list, rslt2);
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
Function fn_484 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_485}}};


// --------- string-list_impl --------------
Function fn_486;
Value *arityImpl_487(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_33);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_33, varArgs0);
Value *rslt1 = arityImpl_213(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_245(empty_list, arg0, (Value *)&_str_34);
Value *rslt3 = protoFnImpl_164(empty_list, rslt2, (Value *)&protoFn_230);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_35);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_35, varArgs4);
Value *rslt5 = arityImpl_213(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_346(empty_list, (Value *)varArgs6);
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
Function fn_486 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_487}}};


// --------- empty?_impl --------------
Function fn_488;
Value *arityImpl_489(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_98(empty_list, arg0);
Value *rslt1 = arityImpl_75(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_488 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_489}}};


// --------- empty_impl --------------
Function fn_490;
Value *arityImpl_491(List *closures, Value *arg0) {
incRef(var_92);
return(var_92);
};


// --------- empty_impl main body --------------
Function fn_490 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_491}}};


// --------- conj_impl --------------
Function fn_492;
Value *arityImpl_493(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_95(empty_list, arg1, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- conj_impl main body --------------
Function fn_492 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_493}}};


// --------- count_impl --------------
Function fn_494;
Value *arityImpl_495(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_98(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_494 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_495}}};


// --------- seq?_impl --------------
Function fn_496;
Value *arityImpl_497(List *closures, Value *arg0) {
incRef(var_38);
return(var_38);
};


// --------- seq?_impl main body --------------
Function fn_496 = {3, -1, "seq?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_497}}};


// --------- seq_impl --------------
Function fn_498;
Value *arityImpl_499(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_498 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_499}}};


// --------- first_impl --------------
Function fn_500;
Value *arityImpl_501(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_101(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- first_impl main body --------------
Function fn_500 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_501}}};


// --------- rest_impl --------------
Function fn_502;
Value *arityImpl_503(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_104(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_502 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_503}}};


// --------- zero_impl --------------
Function fn_504;
Value *arityImpl_505(List *closures, Value *arg0) {
incRef(var_92);
return(var_92);
};


// --------- zero_impl main body --------------
Function fn_504 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_505}}};


// --------- comp*_impl --------------
Function fn_506;
Value *arityImpl_507(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_95(empty_list, arg0, arg1);
Value *rslt1 = arityImpl_471(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_506 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_507}}};


// --------- map_impl --------------
Function fn_508;
Value *arityImpl_509(List *closures, Value *arg0, Value *arg1) {
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
Function fn_508 = {3, -1, "map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_509}}};


// --------- wrap_impl --------------
Function fn_510;
Value *arityImpl_511(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
Value *rslt1 = arityImpl_213(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- wrap_impl main body --------------
Function fn_510 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_511}}};


// --------- flat-map_impl --------------
Function fn_512;
Value *arityImpl_513(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_221(empty_list, arg0, arg1);
Value *cond1;
Value *rslt5 = protoFnImpl_275(empty_list, rslt0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_92);
cond1 = var_92;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt2 = arityImpl_101(empty_list, rslt0);
Value *rslt3 = arityImpl_104(empty_list, rslt0);
Value *rslt4 = protoFnImpl_343(empty_list, rslt2, rslt3);
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
Function fn_512 = {3, -1, "flat-map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_513}}};


// --------- some --------------
Function fn_514;
Value *arityImpl_515(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg0);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_315(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_320(empty_list, arg0);
Value *rslt2 = arityImpl_515(closures, rslt1, arg1);
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
Function fn_514 = {3, -1, "some", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_515}}};


// --------- inc --------------
Function fn_517;
Value *arityImpl_518(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_81(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- inc main body --------------
Function fn_517 = {3, -1, "inc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_518}}};


// --------- + --------------
Function fn_520;
Value *arityImpl_521(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_275(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_393(empty_list, arg0, (Value *)&_num_10, (Value *)&fn_80);
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
Function fn_520 = {3, -1, "+", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_521}}};


// --------- * --------------
Function fn_523;
Value *arityImpl_524(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt1 = arityImpl_393(empty_list, arg0, (Value *)&_num_1, (Value *)&fn_86);
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
Function fn_523 = {3, -1, "*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_524}}};


// --------- dec --------------
Function fn_526;
Value *arityImpl_527(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_84(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- dec main body --------------
Function fn_526 = {3, -1, "dec", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_527}}};


// --------- - --------------
Function fn_529;
Value *arityImpl_530(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt6 = protoFnImpl_275(empty_list, arg0);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_315(empty_list, arg0);
Value *rslt2 = protoFnImpl_320(empty_list, arg0);
Value *cond3;
Value *rslt5 = protoFnImpl_275(empty_list, rslt2);
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
Value *rslt4 = arityImpl_393(empty_list, rslt2, rslt1, (Value *)&fn_83);
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
Function fn_529 = {3, -1, "-", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_530}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_36 = {1, -1, 0,""};

// --------- =*_impl --------------
Function fn_532;
Value *arityImpl_533(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_116(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_532 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_533}}};


// --------- empty?_impl --------------
Function fn_534;
Value *arityImpl_535(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_113(empty_list, arg0);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_534 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_535}}};


// --------- empty_impl --------------
Function fn_536;
Value *arityImpl_537(List *closures, Value *arg0) {
incRef((Value *)&_str_36);
return((Value *)&_str_36);
};


// --------- empty_impl main body --------------
Function fn_536 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_537}}};


// --------- count_impl --------------
Function fn_538;
Value *arityImpl_539(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_113(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_538 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_539}}};


// --------- conj_impl --------------
Function fn_540;
Value *arityImpl_541(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_213(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_164(empty_list, rslt1, (Value *)&protoFn_230);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_345);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_345, varArgs3);
Value *rslt4 = arityImpl_207(empty_list, (Value *)varArgs3);
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
Function fn_540 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_541}}};


// --------- seq_impl --------------
Function fn_542;
Value *arityImpl_543(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_379(empty_list, arg0, (Value *)&_str_36);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_69(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
Value *rslt2 = arityImpl_68(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_310(empty_list, rslt2);
Value *rslt4 = arityImpl_95(empty_list, rslt1, rslt3);
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
Function fn_542 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_543}}};


// --------- first_impl --------------
Function fn_544;
Value *arityImpl_545(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = arityImpl_379(empty_list, arg0, (Value *)&_str_36);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = arityImpl_59(empty_list);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt3);
my_free(rslt3);
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_69(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
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
Function fn_544 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_545}}};


// --------- rest_impl --------------
Function fn_546;
Value *arityImpl_547(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_68(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_546 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_547}}};


// --------- string-list_impl --------------
Function fn_548;
Value *arityImpl_549(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_213(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_548 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_549}}};


// --------- comp*_impl --------------
Function fn_550;

// --------- anon --------------
Function fn_552;
Value *arityImpl_553(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_113(empty_list, arg1);
Value *rslt1 = arityImpl_81(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_552 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_553}}};


// --------- anon --------------
Function fn_554;
Value *arityImpl_555(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_125(empty_list, val0, arg0);
incRef((Value *)&_num_10);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_10);
};

Value *arityImpl_551(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_242(empty_list, arg1);
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
Value *rslt1 = arityImpl_95(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_164(empty_list, rslt1, (Value *)&protoFn_230);
Value *rslt4 = arityImpl_393(empty_list, rslt2, (Value *)&_num_10, (Value *)&fn_552);
Value *rslt5 = arityImpl_122(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_555;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_554 = malloc_function(1);
fn_554->type = 3;
fn_554->name = "anon";
fn_554->arityCount = 1;
fn_554->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_221(empty_list, rslt2, (Value *)fn_554);
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
decRef((Value *)fn_554);
my_free((Value *)fn_554);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_550 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_551}}};


// --------- string-list_impl --------------
Function fn_556;
Value *arityImpl_557(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_213(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_556 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_557}}};


// --------- =*_impl --------------
Function fn_558;
Value *arityImpl_559(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_116(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_558 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_559}}};


// --------- empty?_impl --------------
Function fn_560;
Value *arityImpl_561(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_113(empty_list, arg0);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_560 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_561}}};


// --------- empty_impl --------------
Function fn_562;
Value *arityImpl_563(List *closures, Value *arg0) {
incRef((Value *)&_str_36);
return((Value *)&_str_36);
};


// --------- empty_impl main body --------------
Function fn_562 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_563}}};


// --------- count_impl --------------
Function fn_564;
Value *arityImpl_565(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_113(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_564 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_565}}};


// --------- conj_impl --------------
Function fn_566;
Value *arityImpl_567(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_213(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_164(empty_list, rslt1, (Value *)&protoFn_230);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_345);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_345, varArgs3);
Value *rslt4 = arityImpl_207(empty_list, (Value *)varArgs3);
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
Function fn_566 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_567}}};


// --------- seq_impl --------------
Function fn_568;
Value *arityImpl_569(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_379(empty_list, arg0, (Value *)&_str_36);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_69(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
Value *rslt2 = arityImpl_68(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_310(empty_list, rslt2);
Value *rslt4 = arityImpl_95(empty_list, rslt1, rslt3);
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
Function fn_568 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_569}}};


// --------- first_impl --------------
Function fn_570;
Value *arityImpl_571(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = arityImpl_379(empty_list, arg0, (Value *)&_str_36);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = arityImpl_59(empty_list);
incRef(rslt3);
cond0 = rslt3;
decRef(rslt3);
my_free(rslt3);
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = arityImpl_69(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
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
Function fn_570 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_571}}};


// --------- rest_impl --------------
Function fn_572;
Value *arityImpl_573(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_68(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_572 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_573}}};


// --------- comp*_impl --------------
Function fn_574;

// --------- anon --------------
Function fn_576;
Value *arityImpl_577(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_113(empty_list, arg1);
Value *rslt1 = arityImpl_81(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_576 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_577}}};


// --------- anon --------------
Function fn_578;
Value *arityImpl_579(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_125(empty_list, val0, arg0);
incRef((Value *)&_num_10);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_10);
};

Value *arityImpl_575(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_242(empty_list, arg1);
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
Value *rslt1 = arityImpl_95(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_164(empty_list, rslt1, (Value *)&protoFn_230);
Value *rslt4 = arityImpl_393(empty_list, rslt2, (Value *)&_num_10, (Value *)&fn_576);
Value *rslt5 = arityImpl_122(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_579;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_578 = malloc_function(1);
fn_578->type = 3;
fn_578->name = "anon";
fn_578->arityCount = 1;
fn_578->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_221(empty_list, rslt2, (Value *)fn_578);
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
decRef((Value *)fn_578);
my_free((Value *)fn_578);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_574 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_575}}};


// --------- str --------------
Function fn_580;

// --------- anon --------------
Function fn_582;
Value *arityImpl_583(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_113(empty_list, arg1);
Value *rslt1 = arityImpl_81(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_582 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_583}}};


// --------- anon --------------
Function fn_584;
Value *arityImpl_585(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_125(empty_list, val0, arg0);
incRef((Value *)&_num_10);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_10);
};

Value *arityImpl_581(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt7 = protoFnImpl_275(empty_list, arg0);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef((Value *)&_str_36);
cond0 = (Value *)&_str_36;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_164(empty_list, arg0, (Value *)&protoFn_230);
Value *rslt3 = arityImpl_393(empty_list, rslt1, (Value *)&_num_10, (Value *)&fn_582);
Value *rslt4 = arityImpl_122(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_585;
incRef((Value *)rslt4);
arity_5->closures = listCons((Value *)rslt4, (List *)arity_5->closures);
Function *fn_584 = malloc_function(1);
fn_584->type = 3;
fn_584->name = "anon";
fn_584->arityCount = 1;
fn_584->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_221(empty_list, rslt1, (Value *)fn_584);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef((Value *)fn_584);
my_free((Value *)fn_584);
decRef(rslt6);
my_free(rslt6);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- str main body --------------
Function fn_580 = {3, -1, "str", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_581}}};


// --------- take --------------
Function fn_587;
Value *arityImpl_588(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt7 = arityImpl_379(empty_list, (Value *)&_num_10, arg1);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_315(empty_list, arg0);
Value *rslt2 = protoFnImpl_320(empty_list, arg0);
Value *rslt3 = arityImpl_527(empty_list, arg1);
Value *rslt4 = arityImpl_588(closures, rslt2, rslt3);
Value *rslt5 = arityImpl_95(empty_list, rslt1, rslt4);
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
Function fn_587 = {3, -1, "take", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_588}}};


// --------- drop --------------
Function fn_590;
Value *arityImpl_591(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_383(empty_list, arg1, (Value *)&_num_1);
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
Value *rslt1 = protoFnImpl_320(empty_list, arg0);
Value *rslt2 = arityImpl_527(empty_list, arg1);
Value *rslt3 = arityImpl_591(closures, rslt1, rslt2);
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
Function fn_590 = {3, -1, "drop", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_591}}};


// --------- split --------------
Function fn_593;
Value *arityImpl_594(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt6 = protoFnImpl_275(empty_list, arg0);
Value *rslt7 = arityImpl_383(empty_list, arg1, (Value *)&_num_1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_376(empty_list, (Value *)varArgs8);
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
Value *rslt10 = arityImpl_404(empty_list, arg2);
List *varArgs11 = empty_list;
incRef((Value *)arg0);
varArgs11 = (List *)listCons((Value *)arg0, varArgs11);
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
Value *rslt12 = arityImpl_213(empty_list, (Value *)varArgs11);
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
Value *rslt1 = protoFnImpl_320(empty_list, arg0);
Value *rslt2 = arityImpl_527(empty_list, arg1);
Value *rslt3 = protoFnImpl_315(empty_list, arg0);
Value *rslt4 = arityImpl_95(empty_list, rslt3, arg2);
Value *rslt5 = arityImpl_594(closures, rslt1, rslt2, rslt4);
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

Value *arityImpl_595(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if(((Value *)&fn_593)->type != 3) {
rslt3 = protoFnImpl_9(empty_list, (Value *)&fn_593, arg0, arg1, var_92);
} else {
FnArity *arity0 = findFnArity((Value *)&fn_593, 3);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType3 *fn2 = (FnType3 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg0, arg1, var_92);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_92);
varArgs1 = (List *)listCons(var_92, varArgs1);
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_593)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- split main body --------------
Function fn_593 = {3, -1, "split", 2, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_594}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_595}}};


// --------- replace-at-nth --------------
Function fn_597;
Value *arityImpl_598(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt9 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt10 = protoFnImpl_291(empty_list, arg0);
Value *rslt11 = arityImpl_527(empty_list, rslt10);
Value *rslt12 = arityImpl_383(empty_list, rslt11, arg1);
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
Value *rslt1 = arityImpl_595(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_315(empty_list, rslt1);
List *varArgs3 = empty_list;
incRef((Value *)arg2);
varArgs3 = (List *)listCons((Value *)arg2, varArgs3);
Value *rslt4 = arityImpl_213(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_323(empty_list, rslt1);
Value *rslt6 = protoFnImpl_320(empty_list, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
incRef((Value *)rslt2);
varArgs7 = (List *)listCons((Value *)rslt2, varArgs7);
Value *rslt8 = arityImpl_346(empty_list, (Value *)varArgs7);
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
Function fn_597 = {3, -1, "replace-at-nth", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_598}}};


// --------- remove-nth --------------
Function fn_600;
Value *arityImpl_601(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt7 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt8 = protoFnImpl_291(empty_list, arg0);
Value *rslt9 = arityImpl_527(empty_list, rslt8);
Value *rslt10 = arityImpl_383(empty_list, rslt9, arg1);
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
Value *rslt1 = arityImpl_595(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_315(empty_list, rslt1);
Value *rslt3 = arityImpl_323(empty_list, rslt1);
Value *rslt4 = protoFnImpl_320(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
Value *rslt6 = arityImpl_346(empty_list, (Value *)varArgs5);
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
Function fn_600 = {3, -1, "remove-nth", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_601}}};


// --------- partition --------------
Function fn_603;
Value *arityImpl_604(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_291(empty_list, arg0);
Value *rslt6 = arityImpl_383(empty_list, rslt5, arg1);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_588(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_591(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_604(closures, rslt2, arg1);
Value *rslt4 = arityImpl_95(empty_list, rslt1, rslt3);
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
Function fn_603 = {3, -1, "partition", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_604}}};


// --------- partition-all --------------
Function fn_606;
Value *arityImpl_607(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_291(empty_list, arg0);
Value *rslt6 = arityImpl_383(empty_list, rslt5, arg1);
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
Value *rslt8 = arityImpl_213(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_588(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_591(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_607(closures, rslt2, arg1);
Value *rslt4 = arityImpl_95(empty_list, rslt1, rslt3);
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
Function fn_606 = {3, -1, "partition-all", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_607}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_37 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_609;
Value *arityImpl_610(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_275(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_str_37);
varArgs6 = (List *)listCons((Value *)(Value *)&_str_37, varArgs6);
Value *rslt7 = arityImpl_259(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
Value *rslt8 = arityImpl_59(empty_list);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt9 = arityImpl_379(empty_list, arg1, (Value *)&_num_10);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_310(empty_list, arg0);
Value *rslt11 = protoFnImpl_315(empty_list, rslt10);
incRef(rslt11);
cond0 = rslt11;
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt1 = protoFnImpl_310(empty_list, arg0);
Value *rslt2 = protoFnImpl_320(empty_list, rslt1);
Value *rslt3 = arityImpl_527(empty_list, arg1);
Value *rslt4 = arityImpl_610(closures, rslt2, rslt3);
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

Value *arityImpl_611(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt6 = arityImpl_379(empty_list, arg1, (Value *)&_num_10);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_310(empty_list, arg0);
Value *rslt8 = protoFnImpl_315(empty_list, rslt7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_310(empty_list, arg0);
Value *rslt2 = protoFnImpl_320(empty_list, rslt1);
Value *rslt3 = arityImpl_527(empty_list, arg1);
Value *rslt4 = arityImpl_611(closures, rslt2, rslt3, arg2);
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
Function fn_609 = {3, -1, "nth", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_610}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_611}}};


// --------- last --------------
Function fn_613;
Value *arityImpl_614(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_291(empty_list, arg0);
Value *rslt1 = arityImpl_527(empty_list, rslt0);
Value *rslt2 = arityImpl_610(empty_list, arg0, rslt1);
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
Function fn_613 = {3, -1, "last", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_614}}};


// --------- butlast --------------
Function fn_616;
Value *arityImpl_617(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt6 = protoFnImpl_291(empty_list, arg0);
Value *rslt7 = arityImpl_379(empty_list, (Value *)&_num_1, rslt6);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_315(empty_list, arg0);
Value *rslt2 = protoFnImpl_320(empty_list, arg0);
Value *rslt3 = arityImpl_617(closures, rslt2);
Value *rslt4 = arityImpl_95(empty_list, rslt1, rslt3);
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
Function fn_616 = {3, -1, "butlast", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_617}}};


// --------- map-assoc --------------
Function fn_619;
Value *arityImpl_620(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = arityImpl_242(empty_list, arg0);
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
Value *rslt7 = arityImpl_213(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
Value *rslt9 = arityImpl_213(empty_list, (Value *)varArgs8);
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
Value *rslt10 = arityImpl_101(empty_list, arg0);
Value *rslt11 = arityImpl_101(empty_list, rslt10);
Value *rslt12 = arityImpl_379(empty_list, rslt11, arg1);
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
Value *rslt14 = arityImpl_213(empty_list, (Value *)varArgs13);
decRef((Value *)varArgs13);
my_free((Value *)varArgs13);
Value *rslt15 = arityImpl_104(empty_list, arg0);
Value *rslt16 = arityImpl_95(empty_list, rslt14, rslt15);
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
Value *rslt1 = arityImpl_101(empty_list, arg0);
Value *rslt2 = arityImpl_104(empty_list, arg0);
Value *rslt3 = arityImpl_620(closures, rslt2, arg1, arg2);
Value *rslt4 = arityImpl_95(empty_list, rslt1, rslt3);
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
Function fn_619 = {3, -1, "map-assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_620}}};


// --------- map-get --------------
Function fn_622;
Value *arityImpl_623(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt3 = arityImpl_242(empty_list, arg0);
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
Value *rslt4 = arityImpl_101(empty_list, arg0);
Value *rslt5 = arityImpl_101(empty_list, rslt4);
Value *rslt6 = arityImpl_379(empty_list, rslt5, arg1);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = arityImpl_101(empty_list, arg0);
Value *rslt8 = arityImpl_104(empty_list, rslt7);
Value *rslt9 = arityImpl_101(empty_list, rslt8);
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
Value *rslt1 = arityImpl_104(empty_list, arg0);
Value *rslt2 = arityImpl_623(closures, rslt1, arg1, arg2);
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
Function fn_622 = {3, -1, "map-get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_623}}};

SubString _kw_3 = {5, -1, 6, 0, ":hm-nf"};

// --------- hash-map= --------------
Function fn_625;
Value *arityImpl_626(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt13 = protoFnImpl_275(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg0);
Value *rslt2 = protoFnImpl_315(empty_list, rslt1);
Value *rslt3 = protoFnImpl_320(empty_list, rslt1);
Value *rslt4 = protoFnImpl_315(empty_list, rslt3);
Value *cond5;
Value *rslt8 = arityImpl_379(empty_list, (Value *)&_kw_3, rslt2);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_10);
cond5 = (Value *)&_num_10;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt9 = arityImpl_379(empty_list, (Value *)&_kw_3, rslt4);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef((Value *)&_num_10);
cond5 = (Value *)&_num_10;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_357(empty_list, arg1, rslt2, (Value *)&_kw_3);
Value *rslt11 = arityImpl_379(empty_list, rslt4, rslt10);
Value *rslt12 = arityImpl_370(empty_list, rslt11);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
incRef((Value *)&_num_10);
cond5 = (Value *)&_num_10;
} else {
decRef(rslt12);
my_free(rslt12);
Value *rslt6 = protoFnImpl_320(empty_list, arg0);
Value *rslt7 = arityImpl_626(closures, rslt6, arg1);
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
Function fn_625 = {3, -1, "hash-map=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_626}}};

ProtoImpls *protoImpls_628;
Value *protoFnImpl_631(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_628);
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
FnArity protoFnArity_632 = {8, -1, 1, (List *)0, 0, protoFnImpl_631};
Function protoFn_629 = {3, -1, ".a-list", 1, {&protoFnArity_632}};

// forward declaration for 'HashMap'
Value *var_633;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_38 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_39 = {1, -1, 1,"{"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_40 = {1, -1, 1,"}"};
Number _num_12 = {2, -1, 13};

// --------- instance?_impl --------------
Function fn_634;
Value *arityImpl_635(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_62(empty_list, arg1);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_12, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_634 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_635}}};

Value *protoImpl_636(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_637 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_636}}};


// --------- invoke_impl --------------
Function fn_638;

// --------- seq_impl --------------
Function fn_640;
Value *arityImpl_641(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_642(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_643 = {3, -1, "seq", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_642}}};


// --------- first_impl --------------
Function fn_644;
Value *arityImpl_645(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_101(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_646(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_647 = {3, -1, "first", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_646}}};


// --------- rest_impl --------------
Function fn_648;
Value *arityImpl_649(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_104(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_650(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_651 = {3, -1, "rest", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_650}}};


// --------- =*_impl --------------
Function fn_652;
Value *arityImpl_653(List *closures, Value *arg0, Value *arg1) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt3 = protoFnImpl_291(empty_list, val1);
Value *rslt4 = protoFnImpl_310(empty_list, arg1);
Value *rslt5 = protoFnImpl_291(empty_list, rslt4);
Value *rslt6 = arityImpl_379(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_370(empty_list, rslt6);
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
incRef((Value *)&_num_10);
cond0 = (Value *)&_num_10;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt2 = arityImpl_626(empty_list, val1, arg1);
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

Value *protoImpl_654(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_655 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_654}}};


// --------- string-list_impl --------------
Function fn_656;

// --------- anon --------------
Function fn_658;
Value *arityImpl_659(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_221(empty_list, arg0, (Value *)&protoFn_230);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_24);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_24, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_245(empty_list, rslt0, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_345);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_345, varArgs4);
Value *rslt5 = arityImpl_207(empty_list, (Value *)varArgs4);
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
Function fn_658 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_659}}};

Value *arityImpl_657(List *closures, Value *arg0) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt15 = arityImpl_242(empty_list, val1);
decRef(rslt15);
my_free(rslt15);

if (isTrue(rslt15)) {
decRef(rslt15);
my_free(rslt15);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_38);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_38, varArgs16);
Value *rslt17 = arityImpl_213(empty_list, (Value *)varArgs16);
decRef((Value *)varArgs16);
my_free((Value *)varArgs16);
incRef(rslt17);
cond0 = rslt17;
decRef(rslt17);
my_free(rslt17);
} else {
decRef(rslt15);
my_free(rslt15);
Value *rslt3 = protoFnImpl_221(empty_list, val1, (Value *)&fn_658);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_34);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_34, varArgs4);
Value *rslt5 = arityImpl_213(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = arityImpl_245(empty_list, rslt3, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)(Value *)&fn_345);
varArgs7 = (List *)listCons((Value *)(Value *)&fn_345, varArgs7);
Value *rslt8 = arityImpl_207(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&_str_39);
varArgs9 = (List *)listCons((Value *)(Value *)&_str_39, varArgs9);
Value *rslt10 = arityImpl_213(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_40);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_40, varArgs11);
Value *rslt12 = arityImpl_213(empty_list, (Value *)varArgs11);
decRef((Value *)varArgs11);
my_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)rslt12);
varArgs13 = (List *)listCons((Value *)rslt12, varArgs13);
incRef((Value *)rslt8);
varArgs13 = (List *)listCons((Value *)rslt8, varArgs13);
incRef((Value *)rslt10);
varArgs13 = (List *)listCons((Value *)rslt10, varArgs13);
Value *rslt14 = arityImpl_346(empty_list, (Value *)varArgs13);
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

Value *protoImpl_660(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_661 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_660}}};


// --------- empty?_impl --------------
Function fn_662;
Value *arityImpl_663(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_275(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_664(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_665 = {3, -1, "empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_664}}};


// --------- count_impl --------------
Function fn_666;
Value *arityImpl_667(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_291(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_668(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_669 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_668}}};


// --------- zero_impl --------------
Function fn_670;
Value *arityImpl_671(List *closures, Value *arg0) {
Value *rslt3;
if((var_633)->type != 3) {
rslt3 = protoFnImpl_5(empty_list, var_633, var_92);
} else {
FnArity *arity0 = findFnArity(var_633, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, var_92);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_92);
varArgs1 = (List *)listCons(var_92, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_633)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- zero_impl main body --------------
Function fn_670 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_671}}};

Value *protoImpl_672(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_673 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_672}}};


// --------- comp*_impl --------------
Function fn_674;

// --------- anon --------------
Function fn_676;

// --------- anon --------------
Function fn_678;
Value *arityImpl_679(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_610(empty_list, arg1, (Value *)&_num_10);
Value *rslt1 = arityImpl_610(empty_list, arg1, (Value *)&_num_1);
Value *rslt2 = protoFnImpl_351(empty_list, arg0, rslt0, rslt1);
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
Function fn_678 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_679}}};

Value *arityImpl_677(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_310(empty_list, arg1);
Value *rslt2 = arityImpl_393(empty_list, rslt0, arg0, (Value *)&fn_678);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_676 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_677}}};

Value *arityImpl_675(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg1);
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
Value *rslt2 = arityImpl_393(empty_list, arg1, arg0, (Value *)&fn_676);
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
Function fn_674 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_675}}};

Value *protoImpl_680(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_681 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_680}}};


// --------- assoc_impl --------------
Function fn_682;
Value *arityImpl_683(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_620(empty_list, val0, arg1, arg2);
Value *rslt5;
if((var_633)->type != 3) {
rslt5 = protoFnImpl_5(empty_list, var_633, rslt1);
} else {
FnArity *arity2 = findFnArity(var_633, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_633)->name);
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

Value *protoImpl_684(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_685 = {3, -1, "assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_684}}};


// --------- get_impl --------------
Function fn_686;
Value *arityImpl_687(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_623(empty_list, val0, arg1, arg2);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_688(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_689 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_688}}};


// --------- keys_impl --------------
Function fn_690;
Value *arityImpl_691(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_221(empty_list, val0, (Value *)&protoFn_313);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_692(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[11])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_693 = {3, -1, "keys", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_692}}};


// --------- vals_impl --------------
Function fn_694;
Value *arityImpl_695(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_221(empty_list, val0, (Value *)&fn_322);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_696(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[12])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_697 = {3, -1, "vals", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_696}}};


// --------- .a-list_impl --------------
Function fn_698;
Value *arityImpl_699(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_700(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[13])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_701 = {3, -1, ".a-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_700}}};

Value *arityImpl_639(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_641;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_640 = malloc_function(1);
fn_640->type = 3;
fn_640->name = "seq_impl";
fn_640->arityCount = 1;
fn_640->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_645;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_644 = malloc_function(1);
fn_644->type = 3;
fn_644->name = "first_impl";
fn_644->arityCount = 1;
fn_644->arities[0] = arity_1;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = 8;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_649;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_648 = malloc_function(1);
fn_648->type = 3;
fn_648->name = "rest_impl";
fn_648->arityCount = 1;
fn_648->arities[0] = arity_2;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_653;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_652 = malloc_function(1);
fn_652->type = 3;
fn_652->name = "=*_impl";
fn_652->arityCount = 1;
fn_652->arities[0] = arity_3;
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 1;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_657;
incRef((Value *)arg1);
arity_4->closures = listCons((Value *)arg1, (List *)arity_4->closures);
Function *fn_656 = malloc_function(1);
fn_656->type = 3;
fn_656->name = "string-list_impl";
fn_656->arityCount = 1;
fn_656->arities[0] = arity_4;
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_663;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_662 = malloc_function(1);
fn_662->type = 3;
fn_662->name = "empty?_impl";
fn_662->arityCount = 1;
fn_662->arities[0] = arity_5;
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_667;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_666 = malloc_function(1);
fn_666->type = 3;
fn_666->name = "count_impl";
fn_666->arityCount = 1;
fn_666->arities[0] = arity_6;
FnArity *arity_9 = malloc_fnArity();
arity_9->type = 8;
arity_9->count = 3;
arity_9->closures = empty_list;
arity_9->variadic = 0;
arity_9->fn = arityImpl_683;
incRef((Value *)arg1);
arity_9->closures = listCons((Value *)arg1, (List *)arity_9->closures);
Function *fn_682 = malloc_function(1);
fn_682->type = 3;
fn_682->name = "assoc_impl";
fn_682->arityCount = 1;
fn_682->arities[0] = arity_9;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = 8;
arity_10->count = 3;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_687;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_686 = malloc_function(1);
fn_686->type = 3;
fn_686->name = "get_impl";
fn_686->arityCount = 1;
fn_686->arities[0] = arity_10;
FnArity *arity_11 = malloc_fnArity();
arity_11->type = 8;
arity_11->count = 1;
arity_11->closures = empty_list;
arity_11->variadic = 0;
arity_11->fn = arityImpl_691;
incRef((Value *)arg1);
arity_11->closures = listCons((Value *)arg1, (List *)arity_11->closures);
Function *fn_690 = malloc_function(1);
fn_690->type = 3;
fn_690->name = "keys_impl";
fn_690->arityCount = 1;
fn_690->arities[0] = arity_11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = 8;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_695;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_694 = malloc_function(1);
fn_694->type = 3;
fn_694->name = "vals_impl";
fn_694->arityCount = 1;
fn_694->arities[0] = arity_12;
FnArity *arity_13 = malloc_fnArity();
arity_13->type = 8;
arity_13->count = 1;
arity_13->closures = empty_list;
arity_13->variadic = 0;
arity_13->fn = arityImpl_699;
incRef((Value *)arg1);
arity_13->closures = listCons((Value *)arg1, (List *)arity_13->closures);
Function *fn_698 = malloc_function(1);
fn_698->type = 3;
fn_698->name = ".a-list_impl";
fn_698->arityCount = 1;
fn_698->arities[0] = arity_13;
Value *reified_14 = (Value *)malloc_reified(14);
((ReifiedVal *)reified_14)->type = 13;
((ReifiedVal *)reified_14)->implCount = 14;
((ReifiedVal *)reified_14)->impls[0] = (Value *)fn_640;
incRef((Value *)fn_640);
((ReifiedVal *)reified_14)->impls[1] = (Value *)fn_644;
incRef((Value *)fn_644);
((ReifiedVal *)reified_14)->impls[2] = (Value *)fn_648;
incRef((Value *)fn_648);
((ReifiedVal *)reified_14)->impls[3] = (Value *)fn_652;
incRef((Value *)fn_652);
((ReifiedVal *)reified_14)->impls[4] = (Value *)fn_656;
incRef((Value *)fn_656);
((ReifiedVal *)reified_14)->impls[5] = (Value *)fn_662;
incRef((Value *)fn_662);
((ReifiedVal *)reified_14)->impls[6] = (Value *)fn_666;
incRef((Value *)fn_666);
((ReifiedVal *)reified_14)->impls[7] = (Value *)&fn_670;
incRef((Value *)&fn_670);
((ReifiedVal *)reified_14)->impls[8] = (Value *)&fn_674;
incRef((Value *)&fn_674);
((ReifiedVal *)reified_14)->impls[9] = (Value *)fn_682;
incRef((Value *)fn_682);
((ReifiedVal *)reified_14)->impls[10] = (Value *)fn_686;
incRef((Value *)fn_686);
((ReifiedVal *)reified_14)->impls[11] = (Value *)fn_690;
incRef((Value *)fn_690);
((ReifiedVal *)reified_14)->impls[12] = (Value *)fn_694;
incRef((Value *)fn_694);
((ReifiedVal *)reified_14)->impls[13] = (Value *)fn_698;
incRef((Value *)fn_698);
incRef(reified_14);
decRef((Value *)fn_640);
my_free((Value *)fn_640);
decRef((Value *)fn_644);
my_free((Value *)fn_644);
decRef((Value *)fn_648);
my_free((Value *)fn_648);
decRef((Value *)fn_652);
my_free((Value *)fn_652);
decRef((Value *)fn_656);
my_free((Value *)fn_656);
decRef((Value *)fn_662);
my_free((Value *)fn_662);
decRef((Value *)fn_666);
my_free((Value *)fn_666);
decRef((Value *)fn_682);
my_free((Value *)fn_682);
decRef((Value *)fn_686);
my_free((Value *)fn_686);
decRef((Value *)fn_690);
my_free((Value *)fn_690);
decRef((Value *)fn_694);
my_free((Value *)fn_694);
decRef((Value *)fn_698);
my_free((Value *)fn_698);
decRef(reified_14);
my_free(reified_14);
return(reified_14);
};


// --------- invoke_impl main body --------------
Function fn_638 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_639}}};

Value *protoImpl_702(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_703 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_702}}};

ReifiedVal reified_704 = {12, -1, 2, {(Value *)&fn_634, (Value *)&fn_638}};
Value *var_633 = (Value *)&reified_704;

// --------- hash-map --------------
Function fn_705;
Value *arityImpl_706(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_604(empty_list, arg0, (Value *)&_num_2);
Value *rslt4;
if((var_633)->type != 3) {
rslt4 = protoFnImpl_5(empty_list, var_633, rslt0);
} else {
FnArity *arity1 = findFnArity(var_633, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_633)->name);
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
Function fn_705 = {3, -1, "hash-map", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_706}}};

SubString _kw_4 = {5, -1, 10, 0, ":not-found"};

// --------- merge-with --------------
Function fn_708;

// --------- anon --------------
Function fn_710;

// --------- anon --------------
Function fn_712;
Value *arityImpl_713(List *closures, Value *arg0, Value *arg1) {
Value *val5 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt13 = protoFnImpl_291(empty_list, arg1);
Value *rslt14 = arityImpl_379(empty_list, (Value *)&_num_2, rslt13);
Value *rslt15 = arityImpl_370(empty_list, rslt14);
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
Value *rslt1 = arityImpl_610(empty_list, arg1, (Value *)&_num_10);
Value *rslt2 = arityImpl_610(empty_list, arg1, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_357(empty_list, arg0, rslt1, (Value *)&_kw_4);
Value *cond4;
Value *rslt11 = arityImpl_379(empty_list, (Value *)&_kw_4, rslt3);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_351(empty_list, arg0, rslt1, rslt2);
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
Value *rslt10 = protoFnImpl_351(empty_list, arg0, rslt1, rslt9);
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

Value *arityImpl_711(List *closures, Value *arg0, Value *arg1) {
Value *val2 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt0 = protoFnImpl_310(empty_list, arg1);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_713;
incRef((Value *)val2);
arity_1->closures = listCons((Value *)val2, (List *)arity_1->closures);
Function *fn_712 = malloc_function(1);
fn_712->type = 3;
fn_712->name = "anon";
fn_712->arityCount = 1;
fn_712->arities[0] = arity_1;
Value *rslt3 = arityImpl_393(empty_list, rslt0, arg0, (Value *)fn_712);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef((Value *)fn_712);
my_free((Value *)fn_712);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *arityImpl_709(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_275(empty_list, arg2);
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
arity_1->fn = arityImpl_711;
incRef((Value *)arg0);
arity_1->closures = listCons((Value *)arg0, (List *)arity_1->closures);
Function *fn_710 = malloc_function(1);
fn_710->type = 3;
fn_710->name = "anon";
fn_710->arityCount = 1;
fn_710->arities[0] = arity_1;
Value *rslt2 = arityImpl_393(empty_list, arg2, arg1, (Value *)fn_710);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_710);
my_free((Value *)fn_710);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- merge-with main body --------------
Function fn_708 = {3, -1, "merge-with", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_709}}};

SubString _kw_5 = {5, -1, 17, 0, ":get-in-not-found"};

// --------- get-in --------------
Function fn_715;
Value *arityImpl_716(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt7 = protoFnImpl_291(empty_list, arg1);
Value *rslt8 = arityImpl_379(empty_list, rslt7, (Value *)&_num_10);
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
Value *rslt9 = protoFnImpl_291(empty_list, arg1);
Value *rslt10 = arityImpl_379(empty_list, rslt9, (Value *)&_num_1);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
Value *rslt11 = protoFnImpl_315(empty_list, arg1);
Value *rslt12 = protoFnImpl_357(empty_list, arg0, rslt11, arg2);
incRef(rslt12);
cond0 = rslt12;
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_315(empty_list, arg1);
Value *rslt2 = protoFnImpl_357(empty_list, arg0, rslt1, (Value *)&_kw_5);
Value *cond3;
Value *rslt6 = arityImpl_379(empty_list, (Value *)&_kw_5, rslt2);
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
Value *rslt4 = protoFnImpl_320(empty_list, arg1);
Value *rslt5 = arityImpl_716(closures, rslt2, rslt4, arg2);
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
Function fn_715 = {3, -1, "get-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_716}}};

SubString _kw_6 = {5, -1, 14, 0, ":update-in-nil"};

// --------- update-in --------------
Function fn_718;
Value *arityImpl_719(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt8 = protoFnImpl_291(empty_list, arg1);
Value *rslt9 = arityImpl_379(empty_list, rslt8, (Value *)&_num_10);
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
Value *rslt10 = protoFnImpl_291(empty_list, arg1);
Value *rslt11 = arityImpl_379(empty_list, rslt10, (Value *)&_num_1);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_315(empty_list, arg1);
Value *rslt13 = protoFnImpl_357(empty_list, arg0, rslt12, (Value *)&_kw_6);
Value *cond14;
Value *rslt20 = arityImpl_379(empty_list, (Value *)&_kw_6, rslt13);
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
Value *rslt19 = protoFnImpl_351(empty_list, arg0, rslt12, rslt18);
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
Value *rslt1 = protoFnImpl_315(empty_list, arg1);
Value *rslt2 = protoFnImpl_357(empty_list, arg0, rslt1, (Value *)&_kw_6);
Value *cond3;
Value *rslt7 = arityImpl_379(empty_list, (Value *)&_kw_6, rslt2);
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
Value *rslt4 = protoFnImpl_320(empty_list, arg1);
Value *rslt5 = arityImpl_719(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_351(empty_list, arg0, rslt1, rslt5);
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
Function fn_718 = {3, -1, "update-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_719}}};

SubString _kw_7 = {5, -1, 13, 0, ":assoc-in-nil"};

// --------- assoc-in --------------
Function fn_721;
Value *arityImpl_722(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt13 = protoFnImpl_291(empty_list, arg1);
Value *rslt14 = arityImpl_379(empty_list, rslt13, (Value *)&_num_10);
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
Value *rslt15 = protoFnImpl_291(empty_list, arg1);
Value *rslt16 = arityImpl_379(empty_list, rslt15, (Value *)&_num_1);
decRef(rslt15);
my_free(rslt15);
decRef(rslt16);
my_free(rslt16);

if (isTrue(rslt16)) {
decRef(rslt16);
my_free(rslt16);
Value *rslt17 = protoFnImpl_315(empty_list, arg1);
Value *rslt18 = protoFnImpl_351(empty_list, arg0, rslt17, arg2);
incRef(rslt18);
cond0 = rslt18;
decRef(rslt17);
my_free(rslt17);
decRef(rslt18);
my_free(rslt18);
} else {
decRef(rslt16);
my_free(rslt16);
Value *rslt1 = protoFnImpl_315(empty_list, arg1);
Value *rslt2 = protoFnImpl_357(empty_list, arg0, rslt1, (Value *)&_kw_7);
Value *cond3;
Value *rslt7 = arityImpl_379(empty_list, (Value *)&_kw_7, rslt2);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
List *varArgs8 = empty_list;
Value *rslt9 = arityImpl_706(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_320(empty_list, arg1);
Value *rslt11 = arityImpl_722(closures, rslt9, rslt10, arg2);
Value *rslt12 = protoFnImpl_351(empty_list, arg0, rslt1, rslt11);
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
Value *rslt4 = protoFnImpl_320(empty_list, arg1);
Value *rslt5 = arityImpl_722(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_351(empty_list, arg0, rslt1, rslt5);
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
Function fn_721 = {3, -1, "assoc-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_722}}};


// --------- =*_impl --------------
Function fn_724;
Value *arityImpl_725(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
Value *rslt1 = arityImpl_62(empty_list, arg1);
Value *rslt2 = arityImpl_379(empty_list, rslt0, rslt1);
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
Function fn_724 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_725}}};

Value *protoImpl_726(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_727 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_726}}};

ReifiedVal reified_728 = {14, -1, 1, {(Value *)&fn_724}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[19];} _str_41 = {1, -1, 18,"Could not look up "};

// --------- =*_impl --------------
Function fn_730;
Value *arityImpl_731(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_119(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_730 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_731}}};


// --------- name_impl --------------
Function fn_732;
Value *arityImpl_733(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_47(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_732 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_733}}};


// --------- string-list_impl --------------
Function fn_734;
Value *arityImpl_735(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_227(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
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
Function fn_734 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_735}}};


// --------- invoke_impl --------------
Function fn_736;
Value *arityImpl_737(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_357(empty_list, arg1, arg0, (Value *)&reified_728);
Value *cond1;
Value *rslt2 = arityImpl_379(empty_list, (Value *)&reified_728, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_41);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_41, varArgs3);
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_59(empty_list);
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
Function fn_736 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_737}}};


// --------- =*_impl --------------
Function fn_738;
Value *arityImpl_739(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_119(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_738 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_739}}};


// --------- name_impl --------------
Function fn_740;
Value *arityImpl_741(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_47(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_740 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_741}}};


// --------- string-list_impl --------------
Function fn_742;
Value *arityImpl_743(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_227(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_213(empty_list, (Value *)varArgs1);
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
Function fn_742 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_743}}};


// --------- invoke_impl --------------
Function fn_744;
Value *arityImpl_745(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_357(empty_list, arg1, arg0, (Value *)&reified_728);
Value *cond1;
Value *rslt2 = arityImpl_379(empty_list, (Value *)&reified_728, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_41);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_41, varArgs3);
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_59(empty_list);
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
Function fn_744 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_745}}};


// --------- invoke_impl --------------
Function fn_746;
Value *arityImpl_747(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_357(empty_list, arg1, arg0, arg2);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- invoke_impl main body --------------
Function fn_746 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_747}}};


// --------- symbol? --------------
Function fn_748;
Value *arityImpl_749(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_7, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- symbol? main body --------------
Function fn_748 = {3, -1, "symbol?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_749}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_42 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_751;
Value *arityImpl_752(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_42);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_42, varArgs0);
Value *rslt1 = arityImpl_581(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_56(empty_list, rslt1);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- keyword main body --------------
Function fn_751 = {3, -1, "keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_752}}};


// --------- keyword? --------------
Function fn_754;
Value *arityImpl_755(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_5, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- keyword? main body --------------
Function fn_754 = {3, -1, "keyword?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_755}}};


// --------- number? --------------
Function fn_757;
Value *arityImpl_758(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_2, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- number? main body --------------
Function fn_757 = {3, -1, "number?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_758}}};


// --------- string? --------------
Function fn_760;
Value *arityImpl_761(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_62(empty_list, arg0);
Value *rslt1 = arityImpl_379(empty_list, (Value *)&_num_1, rslt0);
Value *rslt2 = arityImpl_62(empty_list, arg0);
Value *rslt3 = arityImpl_379(empty_list, (Value *)&_num_6, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)rslt1);
varArgs4 = (List *)listCons((Value *)rslt1, varArgs4);
Value *rslt5 = arityImpl_376(empty_list, (Value *)varArgs4);
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
Function fn_760 = {3, -1, "string?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_761}}};


// --------- range* --------------
Function fn_763;
Value *arityImpl_764(List *closures, Value *arg0) {
Value *cond0;
Value *rslt4 = arityImpl_379(empty_list, (Value *)&_num_10, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_num_10);
varArgs5 = (List *)listCons((Value *)(Value *)&_num_10, varArgs5);
Value *rslt6 = arityImpl_213(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = arityImpl_527(empty_list, arg0);
Value *rslt2 = arityImpl_764(closures, rslt1);
Value *rslt3 = arityImpl_95(empty_list, arg0, rslt2);
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
Function fn_763 = {3, -1, "range*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_764}}};


// --------- range --------------
Function fn_766;
Value *arityImpl_767(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_527(empty_list, arg0);
Value *rslt1 = arityImpl_764(empty_list, rslt0);
Value *rslt2 = arityImpl_404(empty_list, rslt1);
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
Function fn_766 = {3, -1, "range", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_767}}};


// --------- repeat --------------
Function fn_769;

// --------- anon --------------
Function fn_771;
Value *arityImpl_772(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *arityImpl_770(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_383(empty_list, arg0, (Value *)&_num_1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_92);
cond0 = var_92;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_527(empty_list, arg0);
Value *rslt2 = arityImpl_764(empty_list, rslt1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_772;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_771 = malloc_function(1);
fn_771->type = 3;
fn_771->name = "anon";
fn_771->arityCount = 1;
fn_771->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_221(empty_list, rslt2, (Value *)fn_771);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_771);
my_free((Value *)fn_771);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- repeat main body --------------
Function fn_769 = {3, -1, "repeat", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_770}}};

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
numInfo = listCons(numberValue(9), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_10"), empty_list);
numInfo = listCons(numberValue(0), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_11"), empty_list);
numInfo = listCons(numberValue(11), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_12"), empty_list);
numInfo = listCons(numberValue(13), numInfo);
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
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_17"), empty_list);
strInfo = listCons(stringValue(":match*-one-arg"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_18"), empty_list);
strInfo = listCons(stringValue(":match*-two-args"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_19"), empty_list);
strInfo = listCons(stringValue("*** 'flat-map' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_20"), empty_list);
strInfo = listCons(stringValue("*** 'wrap' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_21"), empty_list);
strInfo = listCons(stringValue("'name' not implemented for type "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_22"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_23"), empty_list);
strInfo = listCons(stringValue("'serialize' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_24"), empty_list);
strInfo = listCons(stringValue(" "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_25"), empty_list);
strInfo = listCons(stringValue("\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_26"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_27"), empty_list);
strInfo = listCons(stringValue("'=*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_28"), empty_list);
strInfo = listCons(stringValue("'<*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_29"), empty_list);
strInfo = listCons(stringValue("'count' not implemented for "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_30"), empty_list);
strInfo = listCons(stringValue("'get' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_31"), empty_list);
strInfo = listCons(stringValue("<Fn: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_32"), empty_list);
strInfo = listCons(stringValue(">"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_33"), empty_list);
strInfo = listCons(stringValue("("), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_34"), empty_list);
strInfo = listCons(stringValue(", "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_35"), empty_list);
strInfo = listCons(stringValue(")"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_36"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_37"), empty_list);
strInfo = listCons(stringValue("'nth' from empty seq"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_38"), empty_list);
strInfo = listCons(stringValue("{}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue("{"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_40"), empty_list);
strInfo = listCons(stringValue("}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
strInfo = listCons(stringValue("Could not look up "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_42"), empty_list);
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
impl = listCons(stringValue("(Value *)&protoFn_453"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_703"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_736"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_746"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_1;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_0"), protoInfo);
protoInfo = listCons(symbolValue("Function/invoke"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_143;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_142"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Variant/bippity"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_149"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_148;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_147"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Variant/match*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_439"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_637"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_156;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_155"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Type/instance?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_162"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_512"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_161;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_160"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Monad/flat-map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_168"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_167;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_166"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Monad/flatten"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_175;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_174"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Comonad/extract"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_180;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_179"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Comonad/extend"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_185;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_184"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Comonad/duplicate"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_192"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_510"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_191;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_190"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Applicative/wrap"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_198"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_419"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_447"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_197;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_196"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Applicative/apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_217"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_508"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_216;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_215"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Functor/map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_225"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_732"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_740"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_224;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_223"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Named/name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_231"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_409"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_425"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_486"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_548"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_556"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_661"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_734"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_742"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_230;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_229"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Stringable/string-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_237"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_236;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_235"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Serializable/serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_262"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_421"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_484"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_532"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_558"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_655"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_727"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_730"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_738"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_261;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_260"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Eq/=*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_268"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_423"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_267;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_266"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Ord/<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_488"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_534"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_560"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_665"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_273;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_272"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Collection/empty?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_490"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_536"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_562"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_278;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_277"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Collection/empty"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_283;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_282"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Collection/destruct"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_289"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_494"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_538"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_564"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_669"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_288;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_287"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Collection/count"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_492"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_540"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_566"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_294;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_293"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Collection/conj"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_303"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_496"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_302;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_301"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Seqable/seq?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_498"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_542"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_568"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_643"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_308;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_307"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Seqable/seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_500"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_544"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_570"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_647"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_313;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_312"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Seqable/first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_502"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_546"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_572"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_651"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_318;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_317"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Seqable/rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_482"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_326;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_325"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Traversable/traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_478"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_331;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_330"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Crushable/crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_411"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_504"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_673"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_336;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_335"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Monoid/zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_413"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_506"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_550"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_574"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_681"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_341;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_340"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Monoid/comp*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_685"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_349;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_348"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Associative/assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_355"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_689"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_354;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_353"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Associative/get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_693"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_360;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_359"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Associative/keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_697"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_365;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_364"), protoInfo);
protoInfo = listCons(symbolValue("core.toc/Associative/vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_451"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_431;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_430"), protoInfo);
protoInfo = listCons(symbolValue("Getter/.v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_701"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_629;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_628"), protoInfo);
protoInfo = listCons(symbolValue("Getter/.a-list"), protoInfo);
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
arityInfo = listCons(stringValue("arityImpl_41"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_40"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_44"), empty_list);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_43"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_47"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_46"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_50"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_49"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_53"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_52"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_56"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_55"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_59"), empty_list);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_58"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_62"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_61"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_65"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_64"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_68"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_69"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_67"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_72"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_71"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_75"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_74"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_78"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_77"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_81"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_80"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_84"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_83"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_87"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_86"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_90"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_89"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_94"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_95"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_93"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_98"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_97"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_101"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_100"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_104"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_103"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_107"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_106"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_110"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_109"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_113"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_112"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_116"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_115"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_119"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_118"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_122"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_121"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_125"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_124"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_128"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_127"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_131"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_130"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_134"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_133"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_137"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_136"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_140"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_139"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_145"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_143"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_151"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_153"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_148"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_158"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_156"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_164"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_161"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_171"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_170"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_172"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_167"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_177"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_175"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_182"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_180"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_187"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_185"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_194"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_191"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_204"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_197"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_207"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_206"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_210"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_209"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_213"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_212"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_221"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_216"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_227"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_224"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_233"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_230"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_239"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_236"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_242"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_241"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_245"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_244"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_250"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_249"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_253"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_252"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_256"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_255"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_259"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_258"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_264"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_261"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_270"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_267"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_275"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_273"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_280"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_278"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_285"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_283"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_291"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_288"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_296"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_294"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_299"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_298"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_305"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_302"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_310"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_308"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_315"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_313"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_320"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_318"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_323"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_322"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_328"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_326"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_333"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_331"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_338"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_336"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_343"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_341"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_346"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_345"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_351"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_349"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_357"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_354"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_362"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_360"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_367"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_365"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_370"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_369"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_373"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_372"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_376"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_375"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_379"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_380"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_378"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_383"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_384"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_382"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_387"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_386"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_390"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_389"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_393"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_392"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_396"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_395"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_399"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_398"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_404"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_403"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_407"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_406"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_410"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_409"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_412"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_411"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_418"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_417"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_414"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_413"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_420"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_419"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_422"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_421"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_424"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_423"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_426"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_425"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_428"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_427"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_433"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_431"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_437"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_436"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_445"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_444"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_441"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_440"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_456"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_455"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_465"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_464"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_461"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_460"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_471"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_470"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_476"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_475"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_474"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_473"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_479"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_478"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_483"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_482"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_485"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_484"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_487"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_486"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_489"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_488"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_491"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_490"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_493"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_492"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_495"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_494"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_497"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_496"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_499"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_498"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_501"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_500"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_503"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_502"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_505"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_504"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_507"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_506"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_509"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_508"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_511"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_510"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_513"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_512"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_515"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_514"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_518"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_517"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_521"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_520"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_524"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_523"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_527"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_526"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_530"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_529"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_533"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_532"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_535"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_534"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_537"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_536"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_539"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_538"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_541"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_540"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_543"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_542"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_545"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_544"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_547"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_546"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_549"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_548"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_553"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_552"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_551"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_550"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_557"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_556"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_559"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_558"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_561"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_560"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_563"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_562"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_565"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_564"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_567"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_566"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_569"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_568"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_571"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_570"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_573"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_572"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_577"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_576"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_575"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_574"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_583"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_582"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_581"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_580"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_588"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_587"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_591"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_590"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_594"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_595"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_593"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_598"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_597"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_601"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_600"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_604"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_603"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_607"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_606"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_610"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_611"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_609"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_614"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_613"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_617"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_616"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_620"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_619"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_623"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_622"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_626"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_625"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_631"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_629"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_635"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_634"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_659"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_658"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_671"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_670"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_679"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_678"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_677"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_676"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_675"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_674"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_639"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_638"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_706"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_705"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_709"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_708"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_716"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_715"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_719"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_718"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_722"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_721"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_725"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_724"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_731"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_730"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_733"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_732"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_735"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_734"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_737"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_736"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_739"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_738"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_741"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_740"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_743"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_742"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_745"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_744"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_747"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_746"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_749"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_748"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_752"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_751"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_755"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_754"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_758"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_757"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_761"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_760"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_764"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_763"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_767"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_766"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_770"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_769"), fnInfo);
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
symInfo = listCons(stringValue("(Value *)&_num_9"), empty_list);
symInfo = listCons(stringValue("Number _num_9"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Opaque"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_1"), empty_list);
symInfo = listCons(stringValue("Function protoFn_1"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_258"), empty_list);
symInfo = listCons(stringValue("Function fn_258"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&_str_16"), empty_list);
symInfo = listCons(stringValue("String _str_16"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("OpaqueVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_38"), empty_list);
symInfo = listCons(stringValue("Value *var_38;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("true"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_39"), empty_list);
symInfo = listCons(stringValue("Value *var_39;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("false"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_40"), empty_list);
symInfo = listCons(stringValue("Function fn_40"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("output-to-file"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_43"), empty_list);
symInfo = listCons(stringValue("Function fn_43"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("standard-output"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_46"), empty_list);
symInfo = listCons(stringValue("Function fn_46"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_49"), empty_list);
symInfo = listCons(stringValue("Function fn_49"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char-code"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_52"), empty_list);
symInfo = listCons(stringValue("Function fn_52"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_55"), empty_list);
symInfo = listCons(stringValue("Function fn_55"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("new-keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_58"), empty_list);
symInfo = listCons(stringValue("Function fn_58"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("abort"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_61"), empty_list);
symInfo = listCons(stringValue("Function fn_61"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-type"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_64"), empty_list);
symInfo = listCons(stringValue("Function fn_64"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_67"), empty_list);
symInfo = listCons(stringValue("Function fn_67"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subs"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_71"), empty_list);
symInfo = listCons(stringValue("Function fn_71"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_74"), empty_list);
symInfo = listCons(stringValue("Function fn_74"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_77"), empty_list);
symInfo = listCons(stringValue("Function fn_77"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-less-than"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_80"), empty_list);
symInfo = listCons(stringValue("Function fn_80"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("add-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_83"), empty_list);
symInfo = listCons(stringValue("Function fn_83"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subtract-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_86"), empty_list);
symInfo = listCons(stringValue("Function fn_86"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("mult-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_89"), empty_list);
symInfo = listCons(stringValue("Function fn_89"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rem"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_92"), empty_list);
symInfo = listCons(stringValue("Value *var_92;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_93"), empty_list);
symInfo = listCons(stringValue("Function fn_93"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cons"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_97"), empty_list);
symInfo = listCons(stringValue("Function fn_97"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_100"), empty_list);
symInfo = listCons(stringValue("Function fn_100"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("car"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_103"), empty_list);
symInfo = listCons(stringValue("Function fn_103"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cdr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_106"), empty_list);
symInfo = listCons(stringValue("Function fn_106"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_109"), empty_list);
symInfo = listCons(stringValue("Function fn_109"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_112"), empty_list);
symInfo = listCons(stringValue("Function fn_112"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_115"), empty_list);
symInfo = listCons(stringValue("Function fn_115"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_118"), empty_list);
symInfo = listCons(stringValue("Function fn_118"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_121"), empty_list);
symInfo = listCons(stringValue("Function fn_121"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-malloc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_124"), empty_list);
symInfo = listCons(stringValue("Function fn_124"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-append"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_127"), empty_list);
symInfo = listCons(stringValue("Function fn_127"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr-err*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_130"), empty_list);
symInfo = listCons(stringValue("Function fn_130"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("slurp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_133"), empty_list);
symInfo = listCons(stringValue("Function fn_133"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_136"), empty_list);
symInfo = listCons(stringValue("Function fn_136"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("escape-chars"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_139"), empty_list);
symInfo = listCons(stringValue("Function fn_139"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_143"), empty_list);
symInfo = listCons(stringValue("Function protoFn_143"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("bippity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_148"), empty_list);
symInfo = listCons(stringValue("Function protoFn_148"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("match*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_156"), empty_list);
symInfo = listCons(stringValue("Function protoFn_156"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_161"), empty_list);
symInfo = listCons(stringValue("Function protoFn_161"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_771"), empty_list);
symInfo = listCons(stringValue("Function fn_771"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_167"), empty_list);
symInfo = listCons(stringValue("Function protoFn_167"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_175"), empty_list);
symInfo = listCons(stringValue("Function protoFn_175"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extract"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_180"), empty_list);
symInfo = listCons(stringValue("Function protoFn_180"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_185"), empty_list);
symInfo = listCons(stringValue("Function protoFn_185"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("duplicate"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_460"), empty_list);
symInfo = listCons(stringValue("Function fn_460"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comprehend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_191"), empty_list);
symInfo = listCons(stringValue("Function protoFn_191"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_197"), empty_list);
symInfo = listCons(stringValue("Function protoFn_197"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_206"), empty_list);
symInfo = listCons(stringValue("Function fn_206"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_209"), empty_list);
symInfo = listCons(stringValue("Function fn_209"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply-to"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_212"), empty_list);
symInfo = listCons(stringValue("Function fn_212"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_216"), empty_list);
symInfo = listCons(stringValue("Function protoFn_216"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_224"), empty_list);
symInfo = listCons(stringValue("Function protoFn_224"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_230"), empty_list);
symInfo = listCons(stringValue("Function protoFn_230"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_236"), empty_list);
symInfo = listCons(stringValue("Function protoFn_236"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_241"), empty_list);
symInfo = listCons(stringValue("Function fn_241"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_244"), empty_list);
symInfo = listCons(stringValue("Function fn_244"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_249"), empty_list);
symInfo = listCons(stringValue("Function fn_249"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("prn"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_252"), empty_list);
symInfo = listCons(stringValue("Function fn_252"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_255"), empty_list);
symInfo = listCons(stringValue("Function fn_255"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_261"), empty_list);
symInfo = listCons(stringValue("Function protoFn_261"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_267"), empty_list);
symInfo = listCons(stringValue("Function protoFn_267"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_273"), empty_list);
symInfo = listCons(stringValue("Function protoFn_273"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_278"), empty_list);
symInfo = listCons(stringValue("Function protoFn_278"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_283"), empty_list);
symInfo = listCons(stringValue("Function protoFn_283"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("destruct"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_288"), empty_list);
symInfo = listCons(stringValue("Function protoFn_288"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_294"), empty_list);
symInfo = listCons(stringValue("Function protoFn_294"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_298"), empty_list);
symInfo = listCons(stringValue("Function fn_298"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_302"), empty_list);
symInfo = listCons(stringValue("Function protoFn_302"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_308"), empty_list);
symInfo = listCons(stringValue("Function protoFn_308"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_313"), empty_list);
symInfo = listCons(stringValue("Function protoFn_313"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_318"), empty_list);
symInfo = listCons(stringValue("Function protoFn_318"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_322"), empty_list);
symInfo = listCons(stringValue("Function fn_322"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("second"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_326"), empty_list);
symInfo = listCons(stringValue("Function protoFn_326"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_331"), empty_list);
symInfo = listCons(stringValue("Function protoFn_331"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_336"), empty_list);
symInfo = listCons(stringValue("Function protoFn_336"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_341"), empty_list);
symInfo = listCons(stringValue("Function protoFn_341"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_345"), empty_list);
symInfo = listCons(stringValue("Function fn_345"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_349"), empty_list);
symInfo = listCons(stringValue("Function protoFn_349"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_354"), empty_list);
symInfo = listCons(stringValue("Function protoFn_354"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_360"), empty_list);
symInfo = listCons(stringValue("Function protoFn_360"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_365"), empty_list);
symInfo = listCons(stringValue("Function protoFn_365"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_369"), empty_list);
symInfo = listCons(stringValue("Function fn_369"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_372"), empty_list);
symInfo = listCons(stringValue("Function fn_372"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("and"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_375"), empty_list);
symInfo = listCons(stringValue("Function fn_375"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("or"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_378"), empty_list);
symInfo = listCons(stringValue("Function fn_378"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_382"), empty_list);
symInfo = listCons(stringValue("Function fn_382"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_386"), empty_list);
symInfo = listCons(stringValue("Function fn_386"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_389"), empty_list);
symInfo = listCons(stringValue("Function fn_389"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_392"), empty_list);
symInfo = listCons(stringValue("Function fn_392"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_395"), empty_list);
symInfo = listCons(stringValue("Function fn_395"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("filter"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_398"), empty_list);
symInfo = listCons(stringValue("Function fn_398"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_403"), empty_list);
symInfo = listCons(stringValue("Function fn_403"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_406"), empty_list);
symInfo = listCons(stringValue("Function fn_406"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_742"), empty_list);
symInfo = listCons(stringValue("Function fn_742"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_670"), empty_list);
symInfo = listCons(stringValue("Function fn_670"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_674"), empty_list);
symInfo = listCons(stringValue("Function fn_674"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_442"), empty_list);
symInfo = listCons(stringValue("Function fn_442"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_738"), empty_list);
symInfo = listCons(stringValue("Function fn_738"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_423"), empty_list);
symInfo = listCons(stringValue("Function fn_423"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_427"), empty_list);
symInfo = listCons(stringValue("Function fn_427"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("any?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_431"), empty_list);
symInfo = listCons(stringValue("Function protoFn_431"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_435"), empty_list);
symInfo = listCons(stringValue("Value *var_435"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ZipList"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_634"), empty_list);
symInfo = listCons(stringValue("Function fn_634"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_746"), empty_list);
symInfo = listCons(stringValue("Function fn_746"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_448"), empty_list);
symInfo = listCons(stringValue("Function fn_448"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_455"), empty_list);
symInfo = listCons(stringValue("Function fn_455"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partial"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_470"), empty_list);
symInfo = listCons(stringValue("Function fn_470"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-concat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_473"), empty_list);
symInfo = listCons(stringValue("Function fn_473"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_478"), empty_list);
symInfo = listCons(stringValue("Function fn_478"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_482"), empty_list);
symInfo = listCons(stringValue("Function fn_482"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_662"), empty_list);
symInfo = listCons(stringValue("Function fn_662"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_562"), empty_list);
symInfo = listCons(stringValue("Function fn_562"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_566"), empty_list);
symInfo = listCons(stringValue("Function fn_566"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_666"), empty_list);
symInfo = listCons(stringValue("Function fn_666"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_496"), empty_list);
symInfo = listCons(stringValue("Function fn_496"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_640"), empty_list);
symInfo = listCons(stringValue("Function fn_640"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_644"), empty_list);
symInfo = listCons(stringValue("Function fn_644"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_648"), empty_list);
symInfo = listCons(stringValue("Function fn_648"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_508"), empty_list);
symInfo = listCons(stringValue("Function fn_508"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_510"), empty_list);
symInfo = listCons(stringValue("Function fn_510"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_512"), empty_list);
symInfo = listCons(stringValue("Function fn_512"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_514"), empty_list);
symInfo = listCons(stringValue("Function fn_514"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("some"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_517"), empty_list);
symInfo = listCons(stringValue("Function fn_517"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("inc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_520"), empty_list);
symInfo = listCons(stringValue("Function fn_520"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_523"), empty_list);
symInfo = listCons(stringValue("Function fn_523"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_526"), empty_list);
symInfo = listCons(stringValue("Function fn_526"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_529"), empty_list);
symInfo = listCons(stringValue("Function fn_529"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("-"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_580"), empty_list);
symInfo = listCons(stringValue("Function fn_580"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_587"), empty_list);
symInfo = listCons(stringValue("Function fn_587"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_590"), empty_list);
symInfo = listCons(stringValue("Function fn_590"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("drop"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_593"), empty_list);
symInfo = listCons(stringValue("Function fn_593"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_597"), empty_list);
symInfo = listCons(stringValue("Function fn_597"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("replace-at-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_600"), empty_list);
symInfo = listCons(stringValue("Function fn_600"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_603"), empty_list);
symInfo = listCons(stringValue("Function fn_603"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_606"), empty_list);
symInfo = listCons(stringValue("Function fn_606"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition-all"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_609"), empty_list);
symInfo = listCons(stringValue("Function fn_609"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_613"), empty_list);
symInfo = listCons(stringValue("Function fn_613"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("last"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_616"), empty_list);
symInfo = listCons(stringValue("Function fn_616"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_619"), empty_list);
symInfo = listCons(stringValue("Function fn_619"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_622"), empty_list);
symInfo = listCons(stringValue("Function fn_622"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_625"), empty_list);
symInfo = listCons(stringValue("Function fn_625"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_629"), empty_list);
symInfo = listCons(stringValue("Function protoFn_629"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_633"), empty_list);
symInfo = listCons(stringValue("Value *var_633"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("HashMap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_682"), empty_list);
symInfo = listCons(stringValue("Function fn_682"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_686"), empty_list);
symInfo = listCons(stringValue("Function fn_686"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_690"), empty_list);
symInfo = listCons(stringValue("Function fn_690"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_694"), empty_list);
symInfo = listCons(stringValue("Function fn_694"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_698"), empty_list);
symInfo = listCons(stringValue("Function fn_698"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_705"), empty_list);
symInfo = listCons(stringValue("Function fn_705"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_708"), empty_list);
symInfo = listCons(stringValue("Function fn_708"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_715"), empty_list);
symInfo = listCons(stringValue("Function fn_715"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_718"), empty_list);
symInfo = listCons(stringValue("Function fn_718"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_721"), empty_list);
symInfo = listCons(stringValue("Function fn_721"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_728"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_728"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-found"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_740"), empty_list);
symInfo = listCons(stringValue("Function fn_740"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_748"), empty_list);
symInfo = listCons(stringValue("Function fn_748"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_751"), empty_list);
symInfo = listCons(stringValue("Function fn_751"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_754"), empty_list);
symInfo = listCons(stringValue("Function fn_754"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_757"), empty_list);
symInfo = listCons(stringValue("Function fn_757"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_760"), empty_list);
symInfo = listCons(stringValue("Function fn_760"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_763"), empty_list);
symInfo = listCons(stringValue("Function fn_763"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_766"), empty_list);
symInfo = listCons(stringValue("Function fn_766"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_769"), empty_list);
symInfo = listCons(stringValue("Function fn_769"), symInfo);
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
typeInfo = listCons(symbolValue("Opaque"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(10), empty_list);
typeInfo = listCons(symbolValue("10"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(11), empty_list);
typeInfo = listCons(symbolValue("ZipList"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(12), empty_list);
typeInfo = listCons(symbolValue("12"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(13), empty_list);
typeInfo = listCons(symbolValue("HashMap"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(14), empty_list);
typeInfo = listCons(symbolValue("14"), typeInfo);
types = listCons((Value *)typeInfo, types);
return((Value *)types);
}


Value *counts() {
List *cnts = empty_list;
cnts = listCons(numberValue(774), cnts);
return((Value *)cnts);
}

