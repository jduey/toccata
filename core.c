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
char *extractStr(Value *v) {
String *newStr = (String *)my_malloc(sizeof(String) + ((String *)v)->len + 5);
if (v->type == StringType)
snprintf(newStr->buffer, ((String *)v)->len + 1, "%s", ((String *)v)->buffer);
else if (v->type == SubStringType)
snprintf(newStr->buffer, ((String *)v)->len + 1, "%s", ((SubString *)v)->buffer);
else {
fprintf(stderr, "\ninvalid type for 'extractStr'\n");
abort();
}
return(newStr->buffer);
}

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
   fprintf(stderr, "\n*** Could not find proto impl for 'type-name' %lld\n", arg0->type);
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'type-name'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_4 = {8, -1, 1, (List *)0, 0, protoFnImpl_3};
Function protoFn_1 = {3, -1, "type-name", 1, {&protoFnArity_4}};

ProtoImpls *protoImpls_5;
Value *protoFnImpl_8(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_9 = {8, -1, 1, (List *)0, 0, protoFnImpl_8};
Value *protoFnImpl_10(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_11 = {8, -1, 2, (List *)0, 0, protoFnImpl_10};
Value *protoFnImpl_12(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_13 = {8, -1, 3, (List *)0, 0, protoFnImpl_12};
Value *protoFnImpl_14(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_15 = {8, -1, 4, (List *)0, 0, protoFnImpl_14};
Value *protoFnImpl_16(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_17 = {8, -1, 5, (List *)0, 0, protoFnImpl_16};
Value *protoFnImpl_18(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_19 = {8, -1, 6, (List *)0, 0, protoFnImpl_18};
Value *protoFnImpl_20(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5, Value *arg6) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_21 = {8, -1, 7, (List *)0, 0, protoFnImpl_20};
Value *protoFnImpl_22(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5, Value *arg6, Value *arg7) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_5);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'invoke' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_23 = {8, -1, 8, (List *)0, 0, protoFnImpl_22};
Function protoFn_6 = {3, -1, "invoke", 8, {&protoFnArity_9,
&protoFnArity_11,
&protoFnArity_13,
&protoFnArity_15,
&protoFnArity_17,
&protoFnArity_19,
&protoFnArity_21,
&protoFnArity_23}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_0 = {1, -1, 6,"String"};
Number _num_1 = {2, -1, 1};
Number _num_2 = {2, -1, 2};
Number _num_3 = {2, -1, 3};
Number _num_4 = {2, -1, 4};
Number _num_5 = {2, -1, 5};
Number _num_6 = {2, -1, 6};
Number _num_7 = {2, -1, 7};
Number _num_8 = {2, -1, 8};
Number _num_9 = {2, -1, 9};

// --------- type-name_impl --------------
Function fn_24;
Value *arityImpl_25(List *closures, Value *arg0) {
incRef((Value *)&_str_0);
return((Value *)&_str_0);
};


// --------- type-name_impl main body --------------
Function fn_24 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_25}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_1 = {1, -1, 6,"Number"};

// --------- type-name_impl --------------
Function fn_26;
Value *arityImpl_27(List *closures, Value *arg0) {
incRef((Value *)&_str_1);
return((Value *)&_str_1);
};


// --------- type-name_impl main body --------------
Function fn_26 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_27}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[9];} _str_2 = {1, -1, 8,"Function"};

// --------- type-name_impl --------------
Function fn_28;
Value *arityImpl_29(List *closures, Value *arg0) {
incRef((Value *)&_str_2);
return((Value *)&_str_2);
};


// --------- type-name_impl main body --------------
Function fn_28 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_29}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_3 = {1, -1, 4,"List"};

// --------- type-name_impl --------------
Function fn_30;
Value *arityImpl_31(List *closures, Value *arg0) {
incRef((Value *)&_str_3);
return((Value *)&_str_3);
};


// --------- type-name_impl main body --------------
Function fn_30 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_31}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_4 = {1, -1, 7,"Keyword"};

// --------- type-name_impl --------------
Function fn_32;
Value *arityImpl_33(List *closures, Value *arg0) {
incRef((Value *)&_str_4);
return((Value *)&_str_4);
};


// --------- type-name_impl main body --------------
Function fn_32 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_33}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_5 = {1, -1, 6,"SubStr"};

// --------- type-name_impl --------------
Function fn_34;
Value *arityImpl_35(List *closures, Value *arg0) {
incRef((Value *)&_str_5);
return((Value *)&_str_5);
};


// --------- type-name_impl main body --------------
Function fn_34 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_35}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_6 = {1, -1, 6,"Symbol"};

// --------- type-name_impl --------------
Function fn_36;
Value *arityImpl_37(List *closures, Value *arg0) {
incRef((Value *)&_str_6);
return((Value *)&_str_6);
};


// --------- type-name_impl main body --------------
Function fn_36 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_37}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_7 = {1, -1, 7,"FnArity"};

// --------- type-name_impl --------------
Function fn_38;
Value *arityImpl_39(List *closures, Value *arg0) {
incRef((Value *)&_str_7);
return((Value *)&_str_7);
};


// --------- type-name_impl main body --------------
Function fn_38 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_39}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_8 = {1, -1, 6,"Opaque"};

// --------- type-name_impl --------------
Function fn_40;
Value *arityImpl_41(List *closures, Value *arg0) {
incRef((Value *)&_str_8);
return((Value *)&_str_8);
};


// --------- type-name_impl main body --------------
Function fn_40 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_41}}};

// forward declaration for 'print-err'
Value *var_42;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_9 = {1, -1, 4,"void"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_10 = {1, -1, 4,"char"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_11 = {1, -1, 6,"char *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[4];} _str_12 = {1, -1, 3,"int"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_13 = {1, -1, 7,"int64_t"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_14 = {1, -1, 52,"typedef struct {int64_t type; int32_t refs;} Value;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_15 = {1, -1, 7,"Value *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[70];} _str_16 = {1, -1, 69,"typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[83];} _str_17 = {1, -1, 82,"typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[99];} _str_18 = {1, -1, 98,"typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[102];} _str_19 = {1, -1, 101,"typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[106];} _str_20 = {1, -1, 105,"typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[108];} _str_21 = {1, -1, 107,"typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[58];} _str_22 = {1, -1, 57,"typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[88];} _str_23 = {1, -1, 87,"typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[89];} _str_24 = {1, -1, 88,"typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[65];} _str_25 = {1, -1, 64,"typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"};
Value *var_61 = (Value *)&trueVal;;
Value *var_62 = (Value *)&falseVal;;

// --------- output-to-file --------------
Function fn_63;
Value *arityImpl_64(List *closures, Value *arg0) {
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
Function fn_63 = {3, -1, "output-to-file", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_64}}};


// --------- standard-output --------------
Function fn_66;
Value *arityImpl_67(List *closures) {
outStream = stdout;
    return((Value *)&trueVal);
};


// --------- standard-output main body --------------
Function fn_66 = {3, -1, "standard-output", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_67}}};


// --------- symkey-name --------------
Function fn_69;
Value *arityImpl_70(List *closures, Value *arg0) {
return(stringValue(((SubString *)arg0)->buffer));
};


// --------- symkey-name main body --------------
Function fn_69 = {3, -1, "symkey-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_70}}};


// --------- char-code --------------
Function fn_72;
Value *arityImpl_73(List *closures, Value *arg0) {
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
Function fn_72 = {3, -1, "char-code", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_73}}};


// --------- symbol --------------
Function fn_75;
Value *arityImpl_76(List *closures, Value *arg0) {
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
Function fn_75 = {3, -1, "symbol", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_76}}};


// --------- new-keyword --------------
Function fn_78;
Value *arityImpl_79(List *closures, Value *arg0) {
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
Function fn_78 = {3, -1, "new-keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_79}}};


// --------- abort --------------
Function fn_81;
Value *arityImpl_82(List *closures) {
abort();
    return(true);
};


// --------- abort main body --------------
Function fn_81 = {3, -1, "abort", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_82}}};


// --------- get-type --------------
Function fn_84;
Value *arityImpl_85(List *closures, Value *arg0) {
return(numberValue(arg0->type));};


// --------- get-type main body --------------
Function fn_84 = {3, -1, "get-type", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_85}}};


// --------- type= --------------
Function fn_87;
Value *arityImpl_88(List *closures, Value *arg0, Value *arg1) {
if (arg0->type == arg1->type)
                   return(true);
                else
                   return(false);
};


// --------- type= main body --------------
Function fn_87 = {3, -1, "type=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_88}}};


// --------- subs --------------
Function fn_90;
Value *arityImpl_91(List *closures, Value *arg0, Value *arg1) {
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

Value *arityImpl_92(List *closures, Value *arg0, Value *arg1, Value *arg2) {
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
Function fn_90 = {3, -1, "subs", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_91}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_92}}};


// --------- number-str --------------
Function fn_94;
Value *arityImpl_95(List *closures, Value *arg0) {
String *numStr = (String *)my_malloc(sizeof(String) + 10);
    snprintf(numStr->buffer, 9, "%lld", ((Number *)arg0)->numVal);
    numStr->type = StringType;
    numStr->len = strlen(numStr->buffer);
    return((Value *)numStr);
};


// --------- number-str main body --------------
Function fn_94 = {3, -1, "number-str", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_95}}};


// --------- number= --------------
Function fn_97;
Value *arityImpl_98(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      return(false);
   } else if (((Number *)arg0)->numVal != ((Number *)arg1)->numVal)
      return(false);
   else
      return(true);
};


// --------- number= main body --------------
Function fn_97 = {3, -1, "number=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_98}}};


// --------- number-less-than --------------
Function fn_100;
Value *arityImpl_101(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'number-less-than'\n");
      abort();
   } else if (((Number *)arg0)->numVal < ((Number *)arg1)->numVal)
      return(true);
   else
      return(false);
};


// --------- number-less-than main body --------------
Function fn_100 = {3, -1, "number-less-than", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_101}}};


// --------- add-numbers --------------
Function fn_103;
Value *arityImpl_104(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'add-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal + ((Number *)arg1)->numVal));
};


// --------- add-numbers main body --------------
Function fn_103 = {3, -1, "add-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_104}}};


// --------- subtract-numbers --------------
Function fn_106;
Value *arityImpl_107(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'subtract-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal - ((Number *)arg1)->numVal));
};


// --------- subtract-numbers main body --------------
Function fn_106 = {3, -1, "subtract-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_107}}};


// --------- mult-numbers --------------
Function fn_109;
Value *arityImpl_110(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\n*** invalid types for 'mult-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal * ((Number *)arg1)->numVal));
};


// --------- mult-numbers main body --------------
Function fn_109 = {3, -1, "mult-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_110}}};


// --------- rem --------------
Function fn_112;
Value *arityImpl_113(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != NumberType ||
        arg1->type != NumberType) {
      fprintf(outStream, "\ninvalid types for 'rem'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal %
                         ((Number *)arg1)->numVal));
};


// --------- rem main body --------------
Function fn_112 = {3, -1, "rem", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_113}}};

Value *var_115 = (Value *)&(List){4,-1,0,0,0};;

// --------- cons --------------
Function fn_116;
Value *arityImpl_117(List *closures, Value *arg0) {
incRef(arg0);
return((Value *)listCons(arg0, empty_list));
};

Value *arityImpl_118(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
incRef(arg1);
return((Value *)listCons(arg0, (List *)arg1));
};


// --------- cons main body --------------
Function fn_116 = {3, -1, "cons", 2, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_117}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_118}}};


// --------- list-count --------------
Function fn_120;
Value *arityImpl_121(List *closures, Value *arg0) {
if (arg0->type != ListType)
      abort();
    else
      return(numberValue(((List *)arg0)->len));};


// --------- list-count main body --------------
Function fn_120 = {3, -1, "list-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_121}}};


// --------- car --------------
Function fn_123;
Value *arityImpl_124(List *closures, Value *arg0) {
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
Function fn_123 = {3, -1, "car", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_124}}};


// --------- cdr --------------
Function fn_126;
Value *arityImpl_127(List *closures, Value *arg0) {
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
Function fn_126 = {3, -1, "cdr", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_127}}};


// --------- fn-name --------------
Function fn_129;
Value *arityImpl_130(List *closures, Value *arg0) {
if (arg0->type != FunctionType) {
      fprintf(stderr, "\n*** invalid type for 'fn-name'\n");
      abort();
    } else
      return(stringValue(((Function *)arg0)->name));
};


// --------- fn-name main body --------------
Function fn_129 = {3, -1, "fn-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_130}}};


// --------- char --------------
Function fn_132;
Value *arityImpl_133(List *closures, Value *arg0) {
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
Function fn_132 = {3, -1, "char", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_133}}};


// --------- str-count --------------
Function fn_135;
Value *arityImpl_136(List *closures, Value *arg0) {
if (arg0->type != StringType && arg0->type != SubStringType ) {
      fprintf(outStream, "\ninvalid type for 'str-count'\n");
      abort();
    }
   return(numberValue(((String *)arg0)->len));
};


// --------- str-count main body --------------
Function fn_135 = {3, -1, "str-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_136}}};


// --------- str= --------------
Function fn_138;
Value *arityImpl_139(List *closures, Value *arg0, Value *arg1) {
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
Function fn_138 = {3, -1, "str=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_139}}};


// --------- symkey= --------------
Function fn_141;
Value *arityImpl_142(List *closures, Value *arg0, Value *arg1) {
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
Function fn_141 = {3, -1, "symkey=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_142}}};


// --------- str-malloc --------------
Function fn_144;
Value *arityImpl_145(List *closures, Value *arg0) {
String *strVal = (String *)my_malloc(sizeof(String) + ((Number *)arg0)->numVal);
    strVal->type = StringType;
    strVal->len = 0;
    strVal->buffer[0] = 0;
    return((Value *)strVal);
};


// --------- str-malloc main body --------------
Function fn_144 = {3, -1, "str-malloc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_145}}};


// --------- str-append --------------
Function fn_147;
Value *arityImpl_148(List *closures, Value *arg0, Value *arg1) {
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
Function fn_147 = {3, -1, "str-append", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_148}}};


// --------- pr-err* --------------
Function fn_150;
Value *arityImpl_151(List *closures, Value *arg0) {
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
Function fn_150 = {3, -1, "pr-err*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_151}}};


// --------- slurp --------------
Function fn_153;
Value *arityImpl_154(List *closures, Value *arg0) {
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
Function fn_153 = {3, -1, "slurp", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_154}}};


// --------- fn-apply --------------
Function fn_156;
Value *arityImpl_157(List *closures, Value *arg0, Value *arg1) {
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
Function fn_156 = {3, -1, "fn-apply", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_157}}};


// --------- escape-chars --------------
Function fn_159;
Value *arityImpl_160(List *closures, Value *arg0) {
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
Function fn_159 = {3, -1, "escape-chars", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_160}}};


// --------- pr* --------------
Function fn_162;
Value *arityImpl_163(List *closures, Value *arg0) {
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
Function fn_162 = {3, -1, "pr*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_163}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[16];} _str_26 = {1, -1, 15,":match*-one-arg"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[17];} _str_27 = {1, -1, 16,":match*-two-args"};
ProtoImpls *protoImpls_165;
Value *protoFnImpl_168(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_165);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'bippity' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_169 = {8, -1, 1, (List *)0, 0, protoFnImpl_168};
Function protoFn_166 = {3, -1, "bippity", 1, {&protoFnArity_169}};

ProtoImpls *protoImpls_170;
Value *arityImpl_173(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_163(empty_list, (Value *)&_str_26);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *protoFnImpl_174(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_170);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'match*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_175 = {8, -1, 1, (List *)0, 0, protoFnImpl_174};
Value *protoFnImpl_176(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_170);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'match*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_177 = {8, -1, 2, (List *)0, 0, protoFnImpl_176};
Function defaultFn_172 = {3, -1, "match*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_173}}};

Function protoFn_171 = {3, -1, "match*", 2, {&protoFnArity_175,
&protoFnArity_177}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_28 = {1, -1, 52,"*** call to 'instance?' with unknown type parameter."};
SubString _kw_0 = {5, -1, 2, 0, ":x"};
ProtoImpls *protoImpls_178;
Value *arityImpl_181(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_85(empty_list, arg0);
Value *rslt4 = arityImpl_98(empty_list, (Value *)&_num_2, rslt3);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
Value *rslt5 = arityImpl_85(empty_list, arg1);
Value *rslt6 = arityImpl_98(empty_list, arg0, rslt5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = arityImpl_163(empty_list, (Value *)&_str_28);
Value *rslt2 = arityImpl_82(empty_list);
incRef(rslt2);
cond0 = rslt2;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoFnImpl_182(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_178);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'instance?' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_183 = {8, -1, 2, (List *)0, 0, protoFnImpl_182};
Function defaultFn_180 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_181}}};

Function protoFn_179 = {3, -1, "instance?", 1, {&protoFnArity_183}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_29 = {1, -1, 28,"'flat-map' not implemented: "};
ProtoImpls *protoImpls_184;
Value *arityImpl_187(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_3(empty_list, arg0);
Value *rslt4;
if((var_42)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_42, (Value *)&_str_29, rslt0);
} else {
FnArity *arity1 = findFnArity(var_42, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_29, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_29);
varArgs2 = (List *)listCons((Value *)&_str_29, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_42)->name);
  abort();
}
}
Value *rslt5 = arityImpl_82(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_188(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_184);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'flat-map' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_189 = {8, -1, 2, (List *)0, 0, protoFnImpl_188};
Function defaultFn_186 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_187}}};

Function protoFn_185 = {3, -1, "flat-map", 1, {&protoFnArity_189}};

ProtoImpls *protoImpls_190;

// --------- anon --------------
Function fn_194;
Value *arityImpl_195(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- anon main body --------------
Function fn_194 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_195}}};

Value *arityImpl_193(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_188(empty_list, arg0, (Value *)&fn_194);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_196(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_190);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'flatten' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_197 = {8, -1, 1, (List *)0, 0, protoFnImpl_196};
Function defaultFn_192 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_193}}};

Function protoFn_191 = {3, -1, "flatten", 1, {&protoFnArity_197}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[30];} _str_30 = {1, -1, 29,"'duplicate' not implemented: "};
ProtoImpls *protoImpls_198;
Value *protoFnImpl_201(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_198);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'extract' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_202 = {8, -1, 1, (List *)0, 0, protoFnImpl_201};
Function protoFn_199 = {3, -1, "extract", 1, {&protoFnArity_202}};

ProtoImpls *protoImpls_203;
Value *protoFnImpl_206(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_203);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'extend' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_207 = {8, -1, 2, (List *)0, 0, protoFnImpl_206};
Function protoFn_204 = {3, -1, "extend", 1, {&protoFnArity_207}};

ProtoImpls *protoImpls_208;
Value *arityImpl_211(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_3(empty_list, arg0);
Value *rslt4;
if((var_42)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_42, (Value *)&_str_30, rslt0);
} else {
FnArity *arity1 = findFnArity(var_42, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_30, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_30);
varArgs2 = (List *)listCons((Value *)&_str_30, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_42)->name);
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

Value *protoFnImpl_212(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_208);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'duplicate' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_213 = {8, -1, 1, (List *)0, 0, protoFnImpl_212};
Function defaultFn_210 = {3, -1, "duplicate", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_211}}};

Function protoFn_209 = {3, -1, "duplicate", 1, {&protoFnArity_213}};

// forward declaration for 'comprehend'
Value *var_214;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_31 = {1, -1, 26,"*** 'wrap' not implemented"};
Number _num_10 = {2, -1, 0};
ProtoImpls *protoImpls_215;
Value *arityImpl_218(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_42)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_42, (Value *)&_str_31);
} else {
FnArity *arity0 = findFnArity(var_42, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_31);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef((Value *)&_str_31);
varArgs1 = (List *)listCons((Value *)&_str_31, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_42)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *protoFnImpl_219(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_215);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'wrap' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_220 = {8, -1, 2, (List *)0, 0, protoFnImpl_219};
Function defaultFn_217 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_218}}};

Function protoFn_216 = {3, -1, "wrap", 1, {&protoFnArity_220}};

ProtoImpls *protoImpls_221;

// --------- anon --------------
Function fn_225;
Value *arityImpl_226(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((var_214)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_214, arg0, val0);
} else {
FnArity *arity1 = findFnArity(var_214, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_214)->name);
  abort();
}
}
incRef(rslt4);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};


// --------- anon --------------
Function fn_227;
Value *arityImpl_228(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((arg0)->type != 3) {
rslt4 = protoFnImpl_8(empty_list, arg0);
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
Value *rslt5 = protoFnImpl_219(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_224(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_121(empty_list, arg1);
Value *rslt4 = arityImpl_98(empty_list, (Value *)&_num_10, rslt3);
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
arity_5->fn = arityImpl_228;
incRef((Value *)arg0);
arity_5->closures = listCons((Value *)arg0, (List *)arity_5->closures);
Function *fn_227 = malloc_function(1);
fn_227->type = 3;
fn_227->name = "anon";
fn_227->arityCount = 1;
fn_227->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_188(empty_list, arg0, (Value *)fn_227);
incRef(rslt6);
cond0 = rslt6;
decRef((Value *)fn_227);
my_free((Value *)fn_227);
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
arity_1->fn = arityImpl_226;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_225 = malloc_function(1);
fn_225->type = 3;
fn_225->name = "anon";
fn_225->arityCount = 1;
fn_225->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_188(empty_list, arg0, (Value *)fn_225);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_225);
my_free((Value *)fn_225);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoFnImpl_229(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_221);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'apply*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_230 = {8, -1, 2, (List *)0, 0, protoFnImpl_229};
Function defaultFn_223 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_224}}};

Function protoFn_222 = {3, -1, "apply*", 1, {&protoFnArity_230}};


// --------- apply --------------
Function fn_231;
Value *arityImpl_232(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = protoFnImpl_229(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- apply main body --------------
Function fn_231 = {3, -1, "apply", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_232}}};


// --------- apply-to --------------
Function fn_234;
Value *arityImpl_235(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt4 = arityImpl_121(empty_list, arg1);
Value *rslt5 = arityImpl_98(empty_list, (Value *)&_num_10, rslt4);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
Value *rslt9;
if((arg0)->type != 3) {
rslt9 = protoFnImpl_8(empty_list, arg0);
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
Value *rslt1 = arityImpl_124(empty_list, arg1);
Value *rslt2 = protoFnImpl_219(empty_list, rslt1, arg0);
Value *rslt3 = protoFnImpl_229(empty_list, rslt2, arg1);
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
Function fn_234 = {3, -1, "apply-to", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_235}}};


// --------- list --------------
Function fn_237;
Value *arityImpl_238(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_237 = {3, -1, "list", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_238}}};

ProtoImpls *protoImpls_240;

// --------- anon --------------
Function fn_244;
Value *arityImpl_245(List *closures, Value *arg0) {
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
rslt5 = protoFnImpl_10(empty_list, val1, arg0);
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
Value *rslt6 = protoFnImpl_219(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_243(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_245;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_244 = malloc_function(1);
fn_244->type = 3;
fn_244->name = "anon";
fn_244->arityCount = 1;
fn_244->arities[0] = arity_0;
Value *rslt1 = protoFnImpl_188(empty_list, arg0, (Value *)fn_244);
incRef(rslt1);
decRef((Value *)fn_244);
my_free((Value *)fn_244);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_246(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_240);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'map' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_247 = {8, -1, 2, (List *)0, 0, protoFnImpl_246};
Function defaultFn_242 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_243}}};

Function protoFn_241 = {3, -1, "map", 1, {&protoFnArity_247}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_32 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_248;
Value *arityImpl_251(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt4;
if((var_42)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_42, (Value *)&_str_32, rslt0);
} else {
FnArity *arity1 = findFnArity(var_42, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_32, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_32);
varArgs2 = (List *)listCons((Value *)&_str_32, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_42)->name);
  abort();
}
}
Value *rslt5 = arityImpl_82(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_252(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_248);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'name' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_253 = {8, -1, 1, (List *)0, 0, protoFnImpl_252};
Function defaultFn_250 = {3, -1, "name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_251}}};

Function protoFn_249 = {3, -1, "name", 1, {&protoFnArity_253}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_33 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_254;
Value *arityImpl_257(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt4;
if((var_42)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_42, (Value *)&_str_33, rslt0);
} else {
FnArity *arity1 = findFnArity(var_42, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_33, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_33);
varArgs2 = (List *)listCons((Value *)&_str_33, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_42)->name);
  abort();
}
}
Value *rslt5 = arityImpl_82(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_258(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_254);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'string-list' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_259 = {8, -1, 1, (List *)0, 0, protoFnImpl_258};
Function defaultFn_256 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_257}}};

Function protoFn_255 = {3, -1, "string-list", 1, {&protoFnArity_259}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_34 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_260;
Value *arityImpl_263(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt4;
if((var_42)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_42, (Value *)&_str_34, rslt0);
} else {
FnArity *arity1 = findFnArity(var_42, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_34, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_34);
varArgs2 = (List *)listCons((Value *)&_str_34, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_42)->name);
  abort();
}
}
Value *rslt5 = arityImpl_82(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_264(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_260);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'serialize' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_265 = {8, -1, 1, (List *)0, 0, protoFnImpl_264};
Function defaultFn_262 = {3, -1, "serialize", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_263}}};

Function protoFn_261 = {3, -1, "serialize", 1, {&protoFnArity_265}};


// --------- list-empty? --------------
Function fn_266;
Value *arityImpl_267(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_121(empty_list, arg0);
Value *rslt1 = arityImpl_98(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- list-empty? main body --------------
Function fn_266 = {3, -1, "list-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_267}}};


// --------- interpose --------------
Function fn_269;

// --------- anon --------------
Function fn_271;
Value *arityImpl_272(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)val0);
varArgs1 = (List *)listCons((Value *)val0, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *arityImpl_270(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = arityImpl_267(empty_list, arg0);
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
Value *rslt1 = arityImpl_124(empty_list, arg0);
Value *rslt2 = arityImpl_127(empty_list, arg0);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_272;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_271 = malloc_function(1);
fn_271->type = 3;
fn_271->name = "anon";
fn_271->arityCount = 1;
fn_271->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_188(empty_list, rslt2, (Value *)fn_271);
Value *rslt5 = arityImpl_118(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_271);
my_free((Value *)fn_271);
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
Function fn_269 = {3, -1, "interpose", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_270}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_35 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_36 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_274;
Value *arityImpl_275(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = protoFnImpl_188(empty_list, arg0, (Value *)&protoFn_261);
Value *rslt1 = arityImpl_270(empty_list, rslt0, (Value *)&_str_35);
Value *rslt2 = protoFnImpl_246(empty_list, rslt1, (Value *)&fn_162);
Value *rslt3 = arityImpl_163(empty_list, (Value *)&_str_36);
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
Function fn_274 = {3, -1, "prn", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_275}}};


// --------- print --------------
Function fn_277;
Value *arityImpl_278(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_270(empty_list, arg0, (Value *)&_str_35);
Value *rslt1 = protoFnImpl_188(empty_list, rslt0, (Value *)&protoFn_255);
Value *rslt2 = protoFnImpl_246(empty_list, rslt1, (Value *)&fn_162);
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
Function fn_277 = {3, -1, "print", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_278}}};


// --------- println --------------
Function fn_280;
Value *arityImpl_281(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_270(empty_list, arg0, (Value *)&_str_35);
Value *rslt1 = protoFnImpl_188(empty_list, rslt0, (Value *)&protoFn_255);
Value *rslt2 = protoFnImpl_246(empty_list, rslt1, (Value *)&fn_162);
Value *rslt3 = arityImpl_163(empty_list, (Value *)&_str_36);
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
Function fn_280 = {3, -1, "println", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_281}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_37 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_283;
Value *arityImpl_284(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_151(empty_list, (Value *)&_str_37);
Value *rslt1 = arityImpl_270(empty_list, arg0, (Value *)&_str_35);
Value *rslt2 = protoFnImpl_188(empty_list, rslt1, (Value *)&protoFn_255);
Value *rslt3 = protoFnImpl_246(empty_list, rslt2, (Value *)&fn_150);
Value *rslt4 = arityImpl_151(empty_list, (Value *)&_str_36);
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
Function fn_283 = {3, -1, "print-err", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_284}}};

Value *var_42 = (Value *)&fn_283;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_38 = {1, -1, 21,"'=*' not implemented:"};
ProtoImpls *protoImpls_285;
Value *arityImpl_288(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_38);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_38, varArgs0);
Value *rslt1 = arityImpl_284(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_82(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_289(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_285);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '=*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_290 = {8, -1, 2, (List *)0, 0, protoFnImpl_289};
Function defaultFn_287 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_288}}};

Function protoFn_286 = {3, -1, "=*", 1, {&protoFnArity_290}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_39 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_291;
Value *arityImpl_294(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_39);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_39, varArgs0);
Value *rslt1 = arityImpl_284(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_82(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_295(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_291);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '<*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_296 = {8, -1, 2, (List *)0, 0, protoFnImpl_295};
Function defaultFn_293 = {3, -1, "<*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_294}}};

Function protoFn_292 = {3, -1, "<*", 1, {&protoFnArity_296}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_40 = {1, -1, 28,"'count' not implemented for "};
ProtoImpls *protoImpls_297;
Value *protoFnImpl_300(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_297);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'empty?' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_301 = {8, -1, 1, (List *)0, 0, protoFnImpl_300};
Function protoFn_298 = {3, -1, "empty?", 1, {&protoFnArity_301}};

ProtoImpls *protoImpls_302;
Value *protoFnImpl_305(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_302);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'empty' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_306 = {8, -1, 1, (List *)0, 0, protoFnImpl_305};
Function protoFn_303 = {3, -1, "empty", 1, {&protoFnArity_306}};

ProtoImpls *protoImpls_307;
Value *protoFnImpl_310(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_307);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'destruct' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_311 = {8, -1, 2, (List *)0, 0, protoFnImpl_310};
Function protoFn_308 = {3, -1, "destruct", 1, {&protoFnArity_311}};

ProtoImpls *protoImpls_312;
Value *arityImpl_315(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_40);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_40, varArgs0);
Value *rslt1 = arityImpl_284(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_82(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_316(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_312);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'count' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_317 = {8, -1, 1, (List *)0, 0, protoFnImpl_316};
Function defaultFn_314 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_315}}};

Function protoFn_313 = {3, -1, "count", 1, {&protoFnArity_317}};

ProtoImpls *protoImpls_318;
Value *protoFnImpl_321(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_318);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'conj' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_322 = {8, -1, 2, (List *)0, 0, protoFnImpl_321};
Function protoFn_319 = {3, -1, "conj", 1, {&protoFnArity_322}};


// --------- not-empty? --------------
Function fn_323;
Value *arityImpl_324(List *closures, Value *arg0) {
Value *cond0;
Value *rslt1 = protoFnImpl_300(empty_list, arg0);
decRef(rslt1);
my_free(rslt1);

if (isTrue(rslt1)) {
decRef(rslt1);
my_free(rslt1);
incRef(var_62);
cond0 = var_62;
} else {
decRef(rslt1);
my_free(rslt1);
incRef(var_61);
cond0 = var_61;
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- not-empty? main body --------------
Function fn_323 = {3, -1, "not-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_324}}};

ProtoImpls *protoImpls_326;
Value *arityImpl_329(List *closures, Value *arg0) {
incRef(var_62);
return(var_62);
};

Value *protoFnImpl_330(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_326);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'seq?' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_331 = {8, -1, 1, (List *)0, 0, protoFnImpl_330};
Function defaultFn_328 = {3, -1, "seq?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_329}}};

Function protoFn_327 = {3, -1, "seq?", 1, {&protoFnArity_331}};

ProtoImpls *protoImpls_332;
Value *protoFnImpl_335(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_332);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'seq' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_336 = {8, -1, 1, (List *)0, 0, protoFnImpl_335};
Function protoFn_333 = {3, -1, "seq", 1, {&protoFnArity_336}};

ProtoImpls *protoImpls_337;
Value *protoFnImpl_340(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_337);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'first' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_341 = {8, -1, 1, (List *)0, 0, protoFnImpl_340};
Function protoFn_338 = {3, -1, "first", 1, {&protoFnArity_341}};

ProtoImpls *protoImpls_342;
Value *protoFnImpl_345(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_342);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'rest' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_346 = {8, -1, 1, (List *)0, 0, protoFnImpl_345};
Function protoFn_343 = {3, -1, "rest", 1, {&protoFnArity_346}};


// --------- second --------------
Function fn_347;
Value *arityImpl_348(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = protoFnImpl_340(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- second main body --------------
Function fn_347 = {3, -1, "second", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_348}}};

ProtoImpls *protoImpls_350;
Value *protoFnImpl_353(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_350);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'traverse' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_354 = {8, -1, 2, (List *)0, 0, protoFnImpl_353};
Function protoFn_351 = {3, -1, "traverse", 1, {&protoFnArity_354}};

ProtoImpls *protoImpls_355;
Value *protoFnImpl_358(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_355);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'crush' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_359 = {8, -1, 2, (List *)0, 0, protoFnImpl_358};
Function protoFn_356 = {3, -1, "crush", 1, {&protoFnArity_359}};

ProtoImpls *protoImpls_360;
Value *protoFnImpl_363(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_360);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'zero' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_364 = {8, -1, 1, (List *)0, 0, protoFnImpl_363};
Function protoFn_361 = {3, -1, "zero", 1, {&protoFnArity_364}};

ProtoImpls *protoImpls_365;
Value *protoFnImpl_368(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_365);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'comp*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_369 = {8, -1, 2, (List *)0, 0, protoFnImpl_368};
Function protoFn_366 = {3, -1, "comp*", 1, {&protoFnArity_369}};


// --------- comp --------------
Function fn_370;
Value *arityImpl_371(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_368(empty_list, arg0, arg1);
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
Function fn_370 = {3, -1, "comp", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_371}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[24];} _str_41 = {1, -1, 23,"'get' not implemented: "};
SubString _kw_1 = {5, -1, 2, 0, ":m"};
SubString _kw_2 = {5, -1, 2, 0, ":k"};
ProtoImpls *protoImpls_373;
Value *protoFnImpl_376(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_373);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'assoc' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_377 = {8, -1, 3, (List *)0, 0, protoFnImpl_376};
Function protoFn_374 = {3, -1, "assoc", 1, {&protoFnArity_377}};

ProtoImpls *protoImpls_378;
Value *arityImpl_381(List *closures, Value *arg0, Value *arg1, Value *arg2) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)(Value *)&_kw_2);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_2, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_kw_1);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_1, varArgs0);
incRef((Value *)(Value *)&_str_41);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_41, varArgs0);
Value *rslt1 = arityImpl_284(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_82(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_382(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_378);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'get' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_383 = {8, -1, 3, (List *)0, 0, protoFnImpl_382};
Function defaultFn_380 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_381}}};

Function protoFn_379 = {3, -1, "get", 1, {&protoFnArity_383}};

ProtoImpls *protoImpls_384;
Value *protoFnImpl_387(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_384);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'keys' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_388 = {8, -1, 1, (List *)0, 0, protoFnImpl_387};
Function protoFn_385 = {3, -1, "keys", 1, {&protoFnArity_388}};

ProtoImpls *protoImpls_389;
Value *protoFnImpl_392(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_389);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'vals' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_393 = {8, -1, 1, (List *)0, 0, protoFnImpl_392};
Function protoFn_390 = {3, -1, "vals", 1, {&protoFnArity_393}};


// --------- not --------------
Function fn_394;
Value *arityImpl_395(List *closures, Value *arg0) {
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
Function fn_394 = {3, -1, "not", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_395}}};


// --------- and --------------
Function fn_397;
Value *arityImpl_398(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt1 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt2 = protoFnImpl_340(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = protoFnImpl_345(empty_list, arg0);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_397);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_397, varArgs4);
Value *rslt5 = arityImpl_232(empty_list, (Value *)varArgs4);
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
Function fn_397 = {3, -1, "and", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_398}}};


// --------- or --------------
Function fn_400;
Value *arityImpl_401(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt4 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt5 = protoFnImpl_340(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)(Value *)&fn_400);
varArgs2 = (List *)listCons((Value *)(Value *)&fn_400, varArgs2);
Value *rslt3 = arityImpl_232(empty_list, (Value *)varArgs2);
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
Function fn_400 = {3, -1, "or", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_401}}};


// --------- = --------------
Function fn_403;
Value *arityImpl_404(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_289(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_405(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_340(empty_list, arg1);
Value *rslt5 = protoFnImpl_289(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_395(empty_list, rslt5);
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
Value *rslt7 = protoFnImpl_316(empty_list, arg1);
Value *rslt8 = arityImpl_98(empty_list, (Value *)&_num_1, rslt7);
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
incRef((Value *)(Value *)&fn_403);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_403, varArgs1);
Value *rslt2 = arityImpl_232(empty_list, (Value *)varArgs1);
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
Function fn_403 = {3, -1, "=", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_404}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_405}}};


// --------- < --------------
Function fn_407;
Value *arityImpl_408(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_295(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_409(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_340(empty_list, arg1);
Value *rslt5 = protoFnImpl_295(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_395(empty_list, rslt5);
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
Value *rslt7 = protoFnImpl_316(empty_list, arg1);
Value *rslt8 = arityImpl_98(empty_list, (Value *)&_num_1, rslt7);
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
incRef((Value *)(Value *)&fn_407);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_407, varArgs1);
Value *rslt2 = arityImpl_232(empty_list, (Value *)varArgs1);
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
Function fn_407 = {3, -1, "<", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_408}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_409}}};


// --------- list** --------------
Function fn_411;
Value *arityImpl_412(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_345(empty_list, arg1);
Value *rslt3 = arityImpl_412(closures, rslt1, rslt2);
Value *rslt4 = arityImpl_118(empty_list, arg0, rslt3);
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
Function fn_411 = {3, -1, "list**", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_412}}};


// --------- list* --------------
Function fn_414;
Value *arityImpl_415(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = arityImpl_412(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- list* main body --------------
Function fn_414 = {3, -1, "list*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_415}}};


// --------- reduce --------------
Function fn_417;
Value *arityImpl_418(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt10 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_345(empty_list, arg0);
Value *rslt6;
if((arg2)->type != 3) {
rslt6 = protoFnImpl_12(empty_list, arg2, arg1, rslt1);
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
Value *rslt9 = protoFnImpl_300(empty_list, rslt2);
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
Value *rslt8 = arityImpl_418(closures, rslt2, rslt6, arg2);
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
Function fn_417 = {3, -1, "reduce", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_418}}};


// --------- filter --------------
Function fn_420;
Value *arityImpl_421(List *closures, Value *arg0, Value *arg1) {
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
            y = protoFnImpl_10(empty_list, arg1, x);
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
Function fn_420 = {3, -1, "filter", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_421}}};


// --------- remove --------------
Function fn_423;

// --------- anon --------------
Function fn_425;
Value *arityImpl_426(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((val0)->type != 3) {
rslt4 = protoFnImpl_10(empty_list, val0, arg0);
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
Value *rslt5 = arityImpl_395(empty_list, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_424(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_426;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_425 = malloc_function(1);
fn_425->type = 3;
fn_425->name = "anon";
fn_425->arityCount = 1;
fn_425->arities[0] = arity_0;
Value *rslt1 = arityImpl_421(empty_list, arg0, (Value *)fn_425);
incRef(rslt1);
decRef((Value *)fn_425);
my_free((Value *)fn_425);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- remove main body --------------
Function fn_423 = {3, -1, "remove", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_424}}};


// --------- reverse --------------
Function fn_428;
Value *arityImpl_429(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_305(empty_list, arg0);
Value *rslt1 = arityImpl_418(empty_list, arg0, rslt0, (Value *)&protoFn_319);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- reverse main body --------------
Function fn_428 = {3, -1, "reverse", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_429}}};


// --------- identity --------------
Function fn_431;
Value *arityImpl_432(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_431 = {3, -1, "identity", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_432}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_42 = {1, -1, 5,"<Fn: "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_43 = {1, -1, 1,">"};

// --------- string-list_impl --------------
Function fn_434;
Value *arityImpl_435(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_130(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_43);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_43, varArgs1);
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
incRef((Value *)(Value *)&_str_42);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_42, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
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
Function fn_434 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_435}}};


// --------- zero_impl --------------
Function fn_436;
Value *arityImpl_437(List *closures, Value *arg0) {
incRef((Value *)&fn_431);
return((Value *)&fn_431);
};


// --------- zero_impl main body --------------
Function fn_436 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_437}}};


// --------- comp*_impl --------------
Function fn_438;

// --------- anon --------------
Function fn_440;

// --------- anon --------------
Function fn_442;
Value *arityImpl_443(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((arg1)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, arg1, arg0);
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
Function fn_442 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_443}}};

Value *arityImpl_441(List *closures, Value *varArgs) {
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
Value *rslt3 = arityImpl_232(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
Value *rslt5 = arityImpl_418(empty_list, val0, rslt3, (Value *)&fn_442);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_439(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_441;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_440 = malloc_function(1);
fn_440->type = 3;
fn_440->name = "anon";
fn_440->arityCount = 1;
fn_440->arities[0] = arity_0;
incRef((Value *)fn_440);
decRef((Value *)fn_440);
my_free((Value *)fn_440);
return((Value *)fn_440);
};


// --------- comp*_impl main body --------------
Function fn_438 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_439}}};


// --------- apply*_impl --------------
Function fn_444;
Value *arityImpl_445(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_300(empty_list, arg1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
Value *rslt9;
if((arg0)->type != 3) {
rslt9 = protoFnImpl_8(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_345(empty_list, arg1);
Value *rslt3 = arityImpl_412(empty_list, rslt1, rslt2);
Value *rslt4 = arityImpl_157(empty_list, arg0, rslt3);
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
Function fn_444 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_445}}};


// --------- =*_impl --------------
Function fn_446;
Value *arityImpl_447(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_98(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_446 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_447}}};


// --------- <*_impl --------------
Function fn_448;
Value *arityImpl_449(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_101(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- <*_impl main body --------------
Function fn_448 = {3, -1, "<*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_449}}};


// --------- string-list_impl --------------
Function fn_450;
Value *arityImpl_451(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_95(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
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
Function fn_450 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_451}}};


// --------- any? --------------
Function fn_452;
Value *arityImpl_453(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_340(empty_list, arg1);
Value *rslt8;
if((arg0)->type != 3) {
rslt8 = protoFnImpl_10(empty_list, arg0, rslt4);
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
Value *rslt1 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = arityImpl_453(closures, arg0, rslt1);
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
Function fn_452 = {3, -1, "any?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_453}}};

ProtoImpls *protoImpls_455;
Value *protoFnImpl_458(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_455);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '.v' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_459 = {8, -1, 1, (List *)0, 0, protoFnImpl_458};
Function protoFn_456 = {3, -1, ".v", 1, {&protoFnArity_459}};

// forward declaration for 'ZipList'
Value *var_460;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_44 = {1, -1, 7,"ZipList"};
Number _num_11 = {2, -1, 11};
SubString _kw_3 = {5, -1, 4, 0, ":nil"};

// --------- instance?_impl --------------
Function fn_461;
Value *arityImpl_462(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_85(empty_list, arg1);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_11, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_461 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_462}}};

Value *protoImpl_463(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_464 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_463}}};


// --------- invoke_impl --------------
Function fn_465;

// --------- apply*_impl --------------
Function fn_467;

// --------- anon --------------
Function fn_469;
Value *arityImpl_470(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = protoFnImpl_300(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_kw_3);
cond0 = (Value *)&_kw_3;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
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
Function fn_469 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_470}}};

Value *arityImpl_468(List *closures, Value *arg0, Value *arg1) {
Value *val4 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt9 = arityImpl_453(empty_list, (Value *)&protoFn_298, arg1);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt2 = protoFnImpl_246(empty_list, arg1, (Value *)&fn_469);
Value *rslt3 = protoFnImpl_246(empty_list, arg1, (Value *)&protoFn_343);
List *varArgs5 = empty_list;
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
incRef((Value *)val4);
varArgs5 = (List *)listCons((Value *)val4, varArgs5);
Value *rslt6 = arityImpl_232(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_229(empty_list, arg0, rslt3);
Value *rslt8 = arityImpl_118(empty_list, rslt6, rslt7);
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

Value *protoImpl_471(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_472 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_471}}};


// --------- type-name_impl --------------
Function fn_473;
Value *arityImpl_474(List *closures, Value *arg0) {
incRef((Value *)&_str_44);
return((Value *)&_str_44);
};


// --------- type-name_impl main body --------------
Function fn_473 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_474}}};

Value *protoImpl_475(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_476 = {3, -1, "type-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_475}}};


// --------- .v_impl --------------
Function fn_477;
Value *arityImpl_478(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_479(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_480 = {3, -1, ".v", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_479}}};

Value *arityImpl_466(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_468;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_467 = malloc_function(1);
fn_467->type = 3;
fn_467->name = "apply*_impl";
fn_467->arityCount = 1;
fn_467->arities[0] = arity_0;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = 8;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_478;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_477 = malloc_function(1);
fn_477->type = 3;
fn_477->name = ".v_impl";
fn_477->arityCount = 1;
fn_477->arities[0] = arity_2;
Value *reified_3 = (Value *)malloc_reified(3);
((ReifiedVal *)reified_3)->type = 11;
((ReifiedVal *)reified_3)->implCount = 3;
((ReifiedVal *)reified_3)->impls[0] = (Value *)fn_467;
incRef((Value *)fn_467);
((ReifiedVal *)reified_3)->impls[1] = (Value *)&fn_473;
incRef((Value *)&fn_473);
((ReifiedVal *)reified_3)->impls[2] = (Value *)fn_477;
incRef((Value *)fn_477);
incRef(reified_3);
decRef((Value *)fn_467);
my_free((Value *)fn_467);
decRef((Value *)fn_477);
my_free((Value *)fn_477);
decRef(reified_3);
my_free(reified_3);
return(reified_3);
};


// --------- invoke_impl main body --------------
Function fn_465 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_466}}};

Value *protoImpl_481(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_482 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_481}}};

ReifiedVal reified_483 = {10, -1, 2, {(Value *)&fn_461, (Value *)&fn_465}};
Value *var_460 = (Value *)&reified_483;

// --------- partial --------------
Function fn_484;

// --------- anon --------------
Function fn_486;
Value *arityImpl_487(List *closures, Value *varArgs) {
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
Value *rslt3 = arityImpl_371(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val0);
varArgs4 = (List *)listCons((Value *)val0, varArgs4);
Value *rslt5 = arityImpl_232(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_485(List *closures, Value *varArgs) {
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
arity_0->fn = arityImpl_487;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_486 = malloc_function(1);
fn_486->type = 3;
fn_486->name = "anon";
fn_486->arityCount = 1;
fn_486->arities[0] = arity_0;
incRef((Value *)fn_486);
decRef((Value *)fn_486);
my_free((Value *)fn_486);
return((Value *)fn_486);
};

// --------- partial main body --------------
Function fn_484 = {3, -1, "partial", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_485}}};


// --------- comprehend --------------
Function fn_489;

// --------- anon --------------
Function fn_491;
Value *arityImpl_492(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_118(empty_list, arg1, arg0);
Value *rslt3 = arityImpl_429(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val1);
varArgs4 = (List *)listCons((Value *)val1, varArgs4);
Value *rslt5 = arityImpl_232(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = protoFnImpl_219(empty_list, val0, rslt5);
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
Function fn_493;

// --------- anon --------------
Function fn_495;
Value *arityImpl_496(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_118(empty_list, arg1, arg0);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)val1);
varArgs3 = (List *)listCons((Value *)val1, varArgs3);
Value *rslt4 = arityImpl_485(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_188(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_494(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_496;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_495 = malloc_function(1);
fn_495->type = 3;
fn_495->name = "anon";
fn_495->arityCount = 1;
fn_495->arities[0] = arity_0;
incRef((Value *)fn_495);
decRef((Value *)fn_495);
my_free((Value *)fn_495);
return((Value *)fn_495);
};


// --------- anon main body --------------
Function fn_493 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_494}}};


// --------- anon --------------
Function fn_497;
Value *arityImpl_498(List *closures, Value *arg0) {
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
rslt5 = protoFnImpl_10(empty_list, val1, arg0);
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
Value *rslt6 = protoFnImpl_219(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_490(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt16 = protoFnImpl_300(empty_list, arg1);
decRef(rslt16);
my_free(rslt16);

if (isTrue(rslt16)) {
decRef(rslt16);
my_free(rslt16);
Value *rslt20;
if((arg0)->type != 3) {
rslt20 = protoFnImpl_8(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_345(empty_list, arg1);
Value *rslt3 = arityImpl_429(empty_list, rslt2);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_492;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
incRef((Value *)rslt1);
arity_4->closures = listCons((Value *)rslt1, (List *)arity_4->closures);
Function *fn_491 = malloc_function(1);
fn_491->type = 3;
fn_491->name = "anon";
fn_491->arityCount = 1;
fn_491->arities[0] = arity_4;
Value *rslt6 = arityImpl_418(empty_list, rslt3, (Value *)fn_491, (Value *)&fn_493);
Value *cond7;
Value *rslt11 = protoFnImpl_316(empty_list, arg1);
Value *rslt12 = arityImpl_98(empty_list, (Value *)&_num_1, rslt11);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
Value *rslt13 = protoFnImpl_340(empty_list, arg1);
FnArity *arity_14 = malloc_fnArity();
arity_14->type = 8;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_498;
incRef((Value *)arg0);
arity_14->closures = listCons((Value *)arg0, (List *)arity_14->closures);
incRef((Value *)rslt1);
arity_14->closures = listCons((Value *)rslt1, (List *)arity_14->closures);
Function *fn_497 = malloc_function(1);
fn_497->type = 3;
fn_497->name = "anon";
fn_497->arityCount = 1;
fn_497->arities[0] = arity_14;
Value *rslt15 = protoFnImpl_188(empty_list, rslt13, (Value *)fn_497);
incRef(rslt15);
cond7 = rslt15;
decRef(rslt13);
my_free(rslt13);
decRef((Value *)fn_497);
my_free((Value *)fn_497);
decRef(rslt15);
my_free(rslt15);
} else {
decRef(rslt12);
my_free(rslt12);
List *varArgs8 = empty_list;
incRef((Value *)var_115);
varArgs8 = (List *)listCons((Value *)var_115, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_485(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_188(empty_list, rslt1, rslt9);
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
decRef((Value *)fn_491);
my_free((Value *)fn_491);
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
Function fn_489 = {3, -1, "comprehend", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_490}}};

Value *var_214 = (Value *)&fn_489;

// --------- list-concat --------------
Function fn_499;
Value *arityImpl_500(List *closures, Value *arg0) {
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
Function fn_499 = {3, -1, "list-concat", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_500}}};


// --------- list=* --------------
Function fn_502;

// --------- anon --------------
Function fn_504;
Value *arityImpl_505(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_340(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- anon main body --------------
Function fn_504 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_505}}};

Value *arityImpl_503(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt4 = protoFnImpl_340(empty_list, arg0);
Value *rslt5 = protoFnImpl_300(empty_list, rslt4);
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
Value *rslt7 = protoFnImpl_246(empty_list, arg0, (Value *)&fn_504);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)(Value *)&fn_403);
varArgs8 = (List *)listCons((Value *)(Value *)&fn_403, varArgs8);
Value *rslt9 = arityImpl_232(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = arityImpl_395(empty_list, rslt9);
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
Value *rslt1 = protoFnImpl_246(empty_list, arg0, (Value *)&protoFn_343);
Value *rslt2 = arityImpl_503(closures, rslt1);
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
Function fn_502 = {3, -1, "list=*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_503}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_45 = {1, -1, 1,"("};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_46 = {1, -1, 2,", "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_47 = {1, -1, 1,")"};

// --------- crush_impl --------------
Function fn_507;

// --------- anon --------------
Function fn_509;
Value *arityImpl_510(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((val0)->type != 3) {
rslt4 = protoFnImpl_10(empty_list, val0, arg1);
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
Value *rslt6 = arityImpl_371(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
decRef(rslt4);
my_free(rslt4);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_508(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_127(empty_list, arg0);
Value *rslt1 = arityImpl_124(empty_list, arg0);
Value *rslt5;
if((arg1)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, arg1, rslt1);
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
arity_6->fn = arityImpl_510;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_509 = malloc_function(1);
fn_509->type = 3;
fn_509->name = "anon";
fn_509->arityCount = 1;
fn_509->arities[0] = arity_6;
Value *rslt7 = arityImpl_418(empty_list, rslt0, rslt5, (Value *)fn_509);
incRef(rslt7);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
decRef((Value *)fn_509);
my_free((Value *)fn_509);
decRef(rslt7);
my_free(rslt7);
return(rslt7);
};


// --------- crush_impl main body --------------
Function fn_507 = {3, -1, "crush_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_508}}};


// --------- traverse_impl --------------
Function fn_511;
Value *arityImpl_512(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_246(empty_list, arg0, arg1);
Value *rslt1 = protoFnImpl_340(empty_list, rslt0);
Value *rslt2 = protoFnImpl_219(empty_list, rslt1, (Value *)&fn_237);
Value *rslt3 = protoFnImpl_229(empty_list, rslt2, rslt0);
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
Function fn_511 = {3, -1, "traverse_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_512}}};


// --------- =*_impl --------------
Function fn_513;
Value *arityImpl_514(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_85(empty_list, arg0);
Value *rslt5 = arityImpl_85(empty_list, arg1);
Value *rslt6 = arityImpl_404(empty_list, rslt4, rslt5);
Value *rslt7 = arityImpl_395(empty_list, rslt6);
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
Value *rslt8 = protoFnImpl_316(empty_list, arg0);
Value *rslt9 = protoFnImpl_316(empty_list, arg1);
Value *rslt10 = arityImpl_98(empty_list, rslt8, rslt9);
Value *rslt11 = arityImpl_395(empty_list, rslt10);
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
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_503(empty_list, rslt2);
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
Function fn_513 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_514}}};


// --------- string-list_impl --------------
Function fn_515;
Value *arityImpl_516(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_45);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_45, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_270(empty_list, arg0, (Value *)&_str_46);
Value *rslt3 = protoFnImpl_188(empty_list, rslt2, (Value *)&protoFn_255);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_47);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_47, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_371(empty_list, (Value *)varArgs6);
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
Function fn_515 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_516}}};


// --------- empty?_impl --------------
Function fn_517;
Value *arityImpl_518(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_121(empty_list, arg0);
Value *rslt1 = arityImpl_98(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_517 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_518}}};


// --------- empty_impl --------------
Function fn_519;
Value *arityImpl_520(List *closures, Value *arg0) {
incRef(var_115);
return(var_115);
};


// --------- empty_impl main body --------------
Function fn_519 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_520}}};


// --------- conj_impl --------------
Function fn_521;
Value *arityImpl_522(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_118(empty_list, arg1, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- conj_impl main body --------------
Function fn_521 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_522}}};


// --------- count_impl --------------
Function fn_523;
Value *arityImpl_524(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_121(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_523 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_524}}};


// --------- seq?_impl --------------
Function fn_525;
Value *arityImpl_526(List *closures, Value *arg0) {
incRef(var_61);
return(var_61);
};


// --------- seq?_impl main body --------------
Function fn_525 = {3, -1, "seq?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_526}}};


// --------- seq_impl --------------
Function fn_527;
Value *arityImpl_528(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_527 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_528}}};


// --------- first_impl --------------
Function fn_529;
Value *arityImpl_530(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_124(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- first_impl main body --------------
Function fn_529 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_530}}};


// --------- rest_impl --------------
Function fn_531;
Value *arityImpl_532(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_127(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_531 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_532}}};


// --------- zero_impl --------------
Function fn_533;
Value *arityImpl_534(List *closures, Value *arg0) {
incRef(var_115);
return(var_115);
};


// --------- zero_impl main body --------------
Function fn_533 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_534}}};


// --------- comp*_impl --------------
Function fn_535;
Value *arityImpl_536(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_118(empty_list, arg0, arg1);
Value *rslt1 = arityImpl_500(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_535 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_536}}};


// --------- map_impl --------------
Function fn_537;
Value *arityImpl_538(List *closures, Value *arg0, Value *arg1) {
List *l = (List *)arg0;
      if (l->len == 0)
        return((Value *)empty_list);
      else {
        List *head = empty_list;
        List *tail;
        for(Value *x = l->head; x != (Value *)0; l = l->tail, x = l->head) {
          Value *y;
          if(arg1->type != 3) {
            y = protoFnImpl_10(empty_list, arg1, x);
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
Function fn_537 = {3, -1, "map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_538}}};


// --------- wrap_impl --------------
Function fn_539;
Value *arityImpl_540(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- wrap_impl main body --------------
Function fn_539 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_540}}};


// --------- flat-map_impl --------------
Function fn_541;
Value *arityImpl_542(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_246(empty_list, arg0, arg1);
Value *cond1;
Value *rslt5 = protoFnImpl_300(empty_list, rslt0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_115);
cond1 = var_115;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt2 = arityImpl_124(empty_list, rslt0);
Value *rslt3 = arityImpl_127(empty_list, rslt0);
Value *rslt4 = protoFnImpl_368(empty_list, rslt2, rslt3);
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
Function fn_541 = {3, -1, "flat-map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_542}}};


// --------- some --------------
Function fn_543;
Value *arityImpl_544(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt4 = protoFnImpl_340(empty_list, arg0);
Value *rslt8;
if((arg1)->type != 3) {
rslt8 = protoFnImpl_10(empty_list, arg1, rslt4);
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
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = arityImpl_544(closures, rslt1, arg1);
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
Function fn_543 = {3, -1, "some", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_544}}};


// --------- inc --------------
Function fn_546;
Value *arityImpl_547(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_104(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- inc main body --------------
Function fn_546 = {3, -1, "inc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_547}}};


// --------- + --------------
Function fn_549;
Value *arityImpl_550(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt1 = arityImpl_418(empty_list, arg0, (Value *)&_num_10, (Value *)&fn_103);
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
Function fn_549 = {3, -1, "+", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_550}}};


// --------- * --------------
Function fn_552;
Value *arityImpl_553(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt1 = arityImpl_418(empty_list, arg0, (Value *)&_num_1, (Value *)&fn_109);
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
Function fn_552 = {3, -1, "*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_553}}};


// --------- dec --------------
Function fn_555;
Value *arityImpl_556(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_107(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- dec main body --------------
Function fn_555 = {3, -1, "dec", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_556}}};


// --------- - --------------
Function fn_558;
Value *arityImpl_559(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt6 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_345(empty_list, arg0);
Value *cond3;
Value *rslt5 = protoFnImpl_300(empty_list, rslt2);
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
Value *rslt4 = arityImpl_418(empty_list, rslt2, rslt1, (Value *)&fn_106);
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
Function fn_558 = {3, -1, "-", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_559}}};

// forward declaration for 'maybe-val'
Value *var_561;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_48 = {1, -1, 9,"<nothing>"};

// --------- string-list_impl --------------
Function fn_562;
Value *arityImpl_563(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_48);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_48, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_562 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_563}}};

Value *protoImpl_564(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_565 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_564}}};


// --------- =*_impl --------------
Function fn_566;
Value *arityImpl_567(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_88(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_566 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_567}}};

Value *protoImpl_568(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_569 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_568}}};


// --------- zero_impl --------------
Function fn_570;
Value *arityImpl_571(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- zero_impl main body --------------
Function fn_570 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_571}}};

Value *protoImpl_572(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_573 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_572}}};


// --------- comp*_impl --------------
Function fn_574;
Value *arityImpl_575(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_345(empty_list, arg1);
Value *rslt3 = protoFnImpl_368(empty_list, rslt1, rslt2);
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


// --------- comp*_impl main body --------------
Function fn_574 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_575}}};

Value *protoImpl_576(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_577 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_576}}};


// --------- map_impl --------------
Function fn_578;
Value *arityImpl_579(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- map_impl main body --------------
Function fn_578 = {3, -1, "map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_579}}};

Value *protoImpl_580(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_581 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_580}}};


// --------- wrap_impl --------------
Function fn_582;
Value *arityImpl_583(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_561)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_561, arg1);
} else {
FnArity *arity0 = findFnArity(var_561, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg1);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_561)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_582 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_583}}};

Value *protoImpl_584(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_585 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_584}}};


// --------- apply*_impl --------------
Function fn_586;
Value *arityImpl_587(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- apply*_impl main body --------------
Function fn_586 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_587}}};

Value *protoImpl_588(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_589 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_588}}};


// --------- flatten_impl --------------
Function fn_590;
Value *arityImpl_591(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- flatten_impl main body --------------
Function fn_590 = {3, -1, "flatten_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_591}}};

Value *protoImpl_592(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_593 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_592}}};


// --------- flat-map_impl --------------
Function fn_594;
Value *arityImpl_595(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- flat-map_impl main body --------------
Function fn_594 = {3, -1, "flat-map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_595}}};

Value *protoImpl_596(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_597 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_596}}};

ReifiedVal reified_598 = {12, -1, 9, {(Value *)&fn_562, (Value *)&fn_566, (Value *)&fn_570, (Value *)&fn_574, (Value *)&fn_578, (Value *)&fn_582, (Value *)&fn_586, (Value *)&fn_590, (Value *)&fn_594}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_49 = {1, -1, 7,"<maybe "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_50 = {1, -1, 9,"maybe-val"};
Number _num_12 = {2, -1, 14};

// --------- instance?_impl --------------
Function fn_600;
Value *arityImpl_601(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_85(empty_list, arg1);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_12, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_600 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_601}}};

Value *protoImpl_602(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_603 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_602}}};


// --------- invoke_impl --------------
Function fn_604;

// --------- string-list_impl --------------
Function fn_606;
Value *arityImpl_607(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_49);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_49, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_458(empty_list, arg0);
Value *rslt3 = protoFnImpl_258(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_43);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_43, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_371(empty_list, (Value *)varArgs6);
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
Function fn_606 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_607}}};

Value *protoImpl_608(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_609 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_608}}};


// --------- =*_impl --------------
Function fn_610;
Value *arityImpl_611(List *closures, Value *arg0, Value *arg1) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt4 = arityImpl_88(empty_list, arg0, arg1);
Value *rslt5 = arityImpl_395(empty_list, rslt4);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_62);
cond0 = var_62;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt2 = protoFnImpl_458(empty_list, arg1);
Value *rslt3 = arityImpl_404(empty_list, val1, rslt2);
incRef(rslt3);
cond0 = rslt3;
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

Value *protoImpl_612(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_613 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_612}}};


// --------- zero_impl --------------
Function fn_614;
Value *arityImpl_615(List *closures, Value *arg0) {
incRef((Value *)&reified_598);
return((Value *)&reified_598);
};


// --------- zero_impl main body --------------
Function fn_614 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_615}}};

Value *protoImpl_616(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_617 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_616}}};


// --------- comp*_impl --------------
Function fn_618;
Value *arityImpl_619(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- comp*_impl main body --------------
Function fn_618 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_619}}};

Value *protoImpl_620(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_621 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_620}}};


// --------- map_impl --------------
Function fn_622;
Value *arityImpl_623(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((arg1)->type != 3) {
rslt4 = protoFnImpl_10(empty_list, arg1, val0);
} else {
FnArity *arity1 = findFnArity(arg1, 1);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
rslt4 = fn3(arity1->closures, val0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(val0);
varArgs2 = (List *)listCons(val0, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
Value *rslt8;
if((var_561)->type != 3) {
rslt8 = protoFnImpl_10(empty_list, var_561, rslt4);
} else {
FnArity *arity5 = findFnArity(var_561, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_561)->name);
  abort();
}
}
incRef(rslt8);
decRef(rslt4);
my_free(rslt4);
decRef(rslt8);
my_free(rslt8);
return(rslt8);
};

Value *protoImpl_624(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_625 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_624}}};


// --------- wrap_impl --------------
Function fn_626;
Value *arityImpl_627(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_561)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_561, arg1);
} else {
FnArity *arity0 = findFnArity(var_561, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg1);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_561)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_626 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_627}}};

Value *protoImpl_628(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_629 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_628}}};


// --------- apply*_impl --------------
Function fn_630;
Value *arityImpl_631(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&reified_598);
varArgs9 = (List *)listCons((Value *)(Value *)&reified_598, varArgs9);
incRef((Value *)(Value *)&fn_403);
varArgs9 = (List *)listCons((Value *)(Value *)&fn_403, varArgs9);
Value *rslt10 = arityImpl_485(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
Value *rslt11 = arityImpl_544(empty_list, arg1, rslt10);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
incRef((Value *)&reified_598);
cond0 = (Value *)&reified_598;
} else {
decRef(rslt11);
my_free(rslt11);
Value *rslt1 = protoFnImpl_458(empty_list, arg0);
Value *rslt2 = protoFnImpl_246(empty_list, arg1, (Value *)&protoFn_456);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)rslt1);
varArgs3 = (List *)listCons((Value *)rslt1, varArgs3);
Value *rslt4 = arityImpl_232(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt8;
if((var_561)->type != 3) {
rslt8 = protoFnImpl_10(empty_list, var_561, rslt4);
} else {
FnArity *arity5 = findFnArity(var_561, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_561)->name);
  abort();
}
}
incRef(rslt8);
cond0 = rslt8;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt8);
my_free(rslt8);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- apply*_impl main body --------------
Function fn_630 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_631}}};

Value *protoImpl_632(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_633 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_632}}};


// --------- flatten_impl --------------
Function fn_634;
Value *arityImpl_635(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_636(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_637 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_636}}};


// --------- flat-map_impl --------------
Function fn_638;
Value *arityImpl_639(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((arg1)->type != 3) {
rslt4 = protoFnImpl_10(empty_list, arg1, val0);
} else {
FnArity *arity1 = findFnArity(arg1, 1);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
rslt4 = fn3(arity1->closures, val0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(val0);
varArgs2 = (List *)listCons(val0, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
incRef(rslt4);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};

Value *protoImpl_640(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_641 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_640}}};


// --------- type-name_impl --------------
Function fn_642;
Value *arityImpl_643(List *closures, Value *arg0) {
incRef((Value *)&_str_50);
return((Value *)&_str_50);
};


// --------- type-name_impl main body --------------
Function fn_642 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_643}}};

Value *protoImpl_644(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_645 = {3, -1, "type-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_644}}};


// --------- .v_impl --------------
Function fn_646;
Value *arityImpl_647(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_648(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_649 = {3, -1, ".v", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_648}}};

Value *arityImpl_605(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_611;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_610 = malloc_function(1);
fn_610->type = 3;
fn_610->name = "=*_impl";
fn_610->arityCount = 1;
fn_610->arities[0] = arity_1;
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_623;
incRef((Value *)arg1);
arity_4->closures = listCons((Value *)arg1, (List *)arity_4->closures);
Function *fn_622 = malloc_function(1);
fn_622->type = 3;
fn_622->name = "map_impl";
fn_622->arityCount = 1;
fn_622->arities[0] = arity_4;
FnArity *arity_7 = malloc_fnArity();
arity_7->type = 8;
arity_7->count = 1;
arity_7->closures = empty_list;
arity_7->variadic = 0;
arity_7->fn = arityImpl_635;
incRef((Value *)arg1);
arity_7->closures = listCons((Value *)arg1, (List *)arity_7->closures);
Function *fn_634 = malloc_function(1);
fn_634->type = 3;
fn_634->name = "flatten_impl";
fn_634->arityCount = 1;
fn_634->arities[0] = arity_7;
FnArity *arity_8 = malloc_fnArity();
arity_8->type = 8;
arity_8->count = 2;
arity_8->closures = empty_list;
arity_8->variadic = 0;
arity_8->fn = arityImpl_639;
incRef((Value *)arg1);
arity_8->closures = listCons((Value *)arg1, (List *)arity_8->closures);
Function *fn_638 = malloc_function(1);
fn_638->type = 3;
fn_638->name = "flat-map_impl";
fn_638->arityCount = 1;
fn_638->arities[0] = arity_8;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = 8;
arity_10->count = 1;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_647;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_646 = malloc_function(1);
fn_646->type = 3;
fn_646->name = ".v_impl";
fn_646->arityCount = 1;
fn_646->arities[0] = arity_10;
Value *reified_11 = (Value *)malloc_reified(11);
((ReifiedVal *)reified_11)->type = 14;
((ReifiedVal *)reified_11)->implCount = 11;
((ReifiedVal *)reified_11)->impls[0] = (Value *)&fn_606;
incRef((Value *)&fn_606);
((ReifiedVal *)reified_11)->impls[1] = (Value *)fn_610;
incRef((Value *)fn_610);
((ReifiedVal *)reified_11)->impls[2] = (Value *)&fn_614;
incRef((Value *)&fn_614);
((ReifiedVal *)reified_11)->impls[3] = (Value *)&fn_618;
incRef((Value *)&fn_618);
((ReifiedVal *)reified_11)->impls[4] = (Value *)fn_622;
incRef((Value *)fn_622);
((ReifiedVal *)reified_11)->impls[5] = (Value *)&fn_626;
incRef((Value *)&fn_626);
((ReifiedVal *)reified_11)->impls[6] = (Value *)&fn_630;
incRef((Value *)&fn_630);
((ReifiedVal *)reified_11)->impls[7] = (Value *)fn_634;
incRef((Value *)fn_634);
((ReifiedVal *)reified_11)->impls[8] = (Value *)fn_638;
incRef((Value *)fn_638);
((ReifiedVal *)reified_11)->impls[9] = (Value *)&fn_642;
incRef((Value *)&fn_642);
((ReifiedVal *)reified_11)->impls[10] = (Value *)fn_646;
incRef((Value *)fn_646);
incRef(reified_11);
decRef((Value *)fn_610);
my_free((Value *)fn_610);
decRef((Value *)fn_622);
my_free((Value *)fn_622);
decRef((Value *)fn_634);
my_free((Value *)fn_634);
decRef((Value *)fn_638);
my_free((Value *)fn_638);
decRef((Value *)fn_646);
my_free((Value *)fn_646);
decRef(reified_11);
my_free(reified_11);
return(reified_11);
};


// --------- invoke_impl main body --------------
Function fn_604 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_605}}};

Value *protoImpl_650(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_651 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_650}}};

ReifiedVal reified_652 = {13, -1, 2, {(Value *)&fn_600, (Value *)&fn_604}};
Value *var_561 = (Value *)&reified_652;
SubString _kw_4 = {5, -1, 13, 0, ":nothing-here"};

// --------- invoke_impl --------------
Function fn_653;
Value *arityImpl_654(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_561)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_561, arg1);
} else {
FnArity *arity0 = findFnArity(var_561, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg1);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_561)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- invoke_impl main body --------------
Function fn_653 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_654}}};

Value *protoImpl_655(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_656 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_655}}};


// --------- instance?_impl --------------
Function fn_657;
Value *arityImpl_658(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_182(empty_list, var_561, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- instance?_impl main body --------------
Function fn_657 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_658}}};

Value *protoImpl_659(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_660 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_659}}};


// --------- zero_impl --------------
Function fn_661;
Value *arityImpl_662(List *closures, Value *arg0) {
incRef((Value *)&reified_598);
return((Value *)&reified_598);
};


// --------- zero_impl main body --------------
Function fn_661 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_662}}};

Value *protoImpl_663(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_664 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_663}}};


// --------- comp*_impl --------------
Function fn_665;
Value *arityImpl_666(List *closures, Value *arg0, Value *arg1) {
incRef((Value *)&_kw_4);
return((Value *)&_kw_4);
};


// --------- comp*_impl main body --------------
Function fn_665 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_666}}};

Value *protoImpl_667(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_668 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_667}}};

ReifiedVal reified_669 = {15, -1, 4, {(Value *)&fn_653, (Value *)&fn_657, (Value *)&fn_661, (Value *)&fn_665}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_51 = {1, -1, 0,""};

// --------- =*_impl --------------
Function fn_671;
Value *arityImpl_672(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_139(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_671 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_672}}};


// --------- empty?_impl --------------
Function fn_673;
Value *arityImpl_674(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_136(empty_list, arg0);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_673 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_674}}};


// --------- empty_impl --------------
Function fn_675;
Value *arityImpl_676(List *closures, Value *arg0) {
incRef((Value *)&_str_51);
return((Value *)&_str_51);
};


// --------- empty_impl main body --------------
Function fn_675 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_676}}};


// --------- count_impl --------------
Function fn_677;
Value *arityImpl_678(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_136(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_677 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_678}}};


// --------- conj_impl --------------
Function fn_679;
Value *arityImpl_680(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_188(empty_list, rslt1, (Value *)&protoFn_255);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_370);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_370, varArgs3);
Value *rslt4 = arityImpl_232(empty_list, (Value *)varArgs3);
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
Function fn_679 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_680}}};


// --------- seq_impl --------------
Function fn_681;
Value *arityImpl_682(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_404(empty_list, arg0, (Value *)&_str_51);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_92(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
Value *rslt2 = arityImpl_91(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_335(empty_list, rslt2);
Value *rslt4 = arityImpl_118(empty_list, rslt1, rslt3);
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
Function fn_681 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_682}}};


// --------- first_impl --------------
Function fn_683;
Value *arityImpl_684(List *closures, Value *arg0) {
Value *cond0;
Value *rslt6 = arityImpl_404(empty_list, arg0, (Value *)&_str_51);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&reified_598);
cond0 = (Value *)&reified_598;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_92(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
Value *rslt5;
if(((Value *)&reified_669)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, (Value *)&reified_669, rslt1);
} else {
FnArity *arity2 = findFnArity((Value *)&reified_669, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&reified_669)->name);
  abort();
}
}
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- first_impl main body --------------
Function fn_683 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_684}}};


// --------- rest_impl --------------
Function fn_685;
Value *arityImpl_686(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_685 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_686}}};


// --------- string-list_impl --------------
Function fn_687;
Value *arityImpl_688(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_687 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_688}}};


// --------- comp*_impl --------------
Function fn_689;

// --------- anon --------------
Function fn_691;
Value *arityImpl_692(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_136(empty_list, arg1);
Value *rslt1 = arityImpl_104(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_691 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_692}}};


// --------- anon --------------
Function fn_693;
Value *arityImpl_694(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_148(empty_list, val0, arg0);
incRef((Value *)&_num_10);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_10);
};

Value *arityImpl_690(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_267(empty_list, arg1);
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
Value *rslt1 = arityImpl_118(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_188(empty_list, rslt1, (Value *)&protoFn_255);
Value *rslt4 = arityImpl_418(empty_list, rslt2, (Value *)&_num_10, (Value *)&fn_691);
Value *rslt5 = arityImpl_145(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_694;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_693 = malloc_function(1);
fn_693->type = 3;
fn_693->name = "anon";
fn_693->arityCount = 1;
fn_693->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_246(empty_list, rslt2, (Value *)fn_693);
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
decRef((Value *)fn_693);
my_free((Value *)fn_693);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_689 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_690}}};


// --------- string-list_impl --------------
Function fn_695;
Value *arityImpl_696(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_695 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_696}}};


// --------- =*_impl --------------
Function fn_697;
Value *arityImpl_698(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_139(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_697 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_698}}};


// --------- empty?_impl --------------
Function fn_699;
Value *arityImpl_700(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_136(empty_list, arg0);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_10, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_699 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_700}}};


// --------- empty_impl --------------
Function fn_701;
Value *arityImpl_702(List *closures, Value *arg0) {
incRef((Value *)&_str_51);
return((Value *)&_str_51);
};


// --------- empty_impl main body --------------
Function fn_701 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_702}}};


// --------- count_impl --------------
Function fn_703;
Value *arityImpl_704(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_136(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_703 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_704}}};


// --------- conj_impl --------------
Function fn_705;
Value *arityImpl_706(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_238(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_188(empty_list, rslt1, (Value *)&protoFn_255);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_370);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_370, varArgs3);
Value *rslt4 = arityImpl_232(empty_list, (Value *)varArgs3);
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
Function fn_705 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_706}}};


// --------- seq_impl --------------
Function fn_707;
Value *arityImpl_708(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_404(empty_list, arg0, (Value *)&_str_51);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_92(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
Value *rslt2 = arityImpl_91(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_335(empty_list, rslt2);
Value *rslt4 = arityImpl_118(empty_list, rslt1, rslt3);
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
Function fn_707 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_708}}};


// --------- first_impl --------------
Function fn_709;
Value *arityImpl_710(List *closures, Value *arg0) {
Value *cond0;
Value *rslt6 = arityImpl_404(empty_list, arg0, (Value *)&_str_51);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&reified_598);
cond0 = (Value *)&reified_598;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_92(empty_list, arg0, (Value *)&_num_10, (Value *)&_num_1);
Value *rslt5;
if(((Value *)&reified_669)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, (Value *)&reified_669, rslt1);
} else {
FnArity *arity2 = findFnArity((Value *)&reified_669, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&reified_669)->name);
  abort();
}
}
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- first_impl main body --------------
Function fn_709 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_710}}};


// --------- rest_impl --------------
Function fn_711;
Value *arityImpl_712(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_711 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_712}}};


// --------- comp*_impl --------------
Function fn_713;

// --------- anon --------------
Function fn_715;
Value *arityImpl_716(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_136(empty_list, arg1);
Value *rslt1 = arityImpl_104(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_715 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_716}}};


// --------- anon --------------
Function fn_717;
Value *arityImpl_718(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_148(empty_list, val0, arg0);
incRef((Value *)&_num_10);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_10);
};

Value *arityImpl_714(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_267(empty_list, arg1);
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
Value *rslt1 = arityImpl_118(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_188(empty_list, rslt1, (Value *)&protoFn_255);
Value *rslt4 = arityImpl_418(empty_list, rslt2, (Value *)&_num_10, (Value *)&fn_715);
Value *rslt5 = arityImpl_145(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_718;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_717 = malloc_function(1);
fn_717->type = 3;
fn_717->name = "anon";
fn_717->arityCount = 1;
fn_717->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_246(empty_list, rslt2, (Value *)fn_717);
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
decRef((Value *)fn_717);
my_free((Value *)fn_717);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_713 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_714}}};


// --------- str --------------
Function fn_719;

// --------- anon --------------
Function fn_721;
Value *arityImpl_722(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_136(empty_list, arg1);
Value *rslt1 = arityImpl_104(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_721 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_722}}};


// --------- anon --------------
Function fn_723;
Value *arityImpl_724(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_148(empty_list, val0, arg0);
incRef((Value *)&_num_10);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_10);
};

Value *arityImpl_720(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt7 = protoFnImpl_300(empty_list, arg0);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef((Value *)&_str_51);
cond0 = (Value *)&_str_51;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_188(empty_list, arg0, (Value *)&protoFn_255);
Value *rslt3 = arityImpl_418(empty_list, rslt1, (Value *)&_num_10, (Value *)&fn_721);
Value *rslt4 = arityImpl_145(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_724;
incRef((Value *)rslt4);
arity_5->closures = listCons((Value *)rslt4, (List *)arity_5->closures);
Function *fn_723 = malloc_function(1);
fn_723->type = 3;
fn_723->name = "anon";
fn_723->arityCount = 1;
fn_723->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_246(empty_list, rslt1, (Value *)fn_723);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef((Value *)fn_723);
my_free((Value *)fn_723);
decRef(rslt6);
my_free(rslt6);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- str main body --------------
Function fn_719 = {3, -1, "str", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_720}}};


// --------- take --------------
Function fn_726;
Value *arityImpl_727(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt7 = arityImpl_404(empty_list, (Value *)&_num_10, arg1);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_345(empty_list, arg0);
Value *rslt3 = arityImpl_556(empty_list, arg1);
Value *rslt4 = arityImpl_727(closures, rslt2, rslt3);
Value *rslt5 = arityImpl_118(empty_list, rslt1, rslt4);
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
Function fn_726 = {3, -1, "take", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_727}}};


// --------- drop --------------
Function fn_729;
Value *arityImpl_730(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_408(empty_list, arg1, (Value *)&_num_1);
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
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = arityImpl_556(empty_list, arg1);
Value *rslt3 = arityImpl_730(closures, rslt1, rslt2);
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
Function fn_729 = {3, -1, "drop", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_730}}};


// --------- split --------------
Function fn_732;
Value *arityImpl_733(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt6 = protoFnImpl_300(empty_list, arg0);
Value *rslt7 = arityImpl_408(empty_list, arg1, (Value *)&_num_1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_401(empty_list, (Value *)varArgs8);
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
Value *rslt10 = arityImpl_429(empty_list, arg2);
List *varArgs11 = empty_list;
incRef((Value *)arg0);
varArgs11 = (List *)listCons((Value *)arg0, varArgs11);
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
Value *rslt12 = arityImpl_238(empty_list, (Value *)varArgs11);
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
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = arityImpl_556(empty_list, arg1);
Value *rslt3 = protoFnImpl_340(empty_list, arg0);
Value *rslt4 = arityImpl_118(empty_list, rslt3, arg2);
Value *rslt5 = arityImpl_733(closures, rslt1, rslt2, rslt4);
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

Value *arityImpl_734(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if(((Value *)&fn_732)->type != 3) {
rslt3 = protoFnImpl_14(empty_list, (Value *)&fn_732, arg0, arg1, var_115);
} else {
FnArity *arity0 = findFnArity((Value *)&fn_732, 3);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType3 *fn2 = (FnType3 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg0, arg1, var_115);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_115);
varArgs1 = (List *)listCons(var_115, varArgs1);
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_732)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- split main body --------------
Function fn_732 = {3, -1, "split", 2, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_733}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_734}}};


// --------- replace-at-nth --------------
Function fn_736;
Value *arityImpl_737(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt9 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt10 = protoFnImpl_316(empty_list, arg0);
Value *rslt11 = arityImpl_556(empty_list, rslt10);
Value *rslt12 = arityImpl_408(empty_list, rslt11, arg1);
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
Value *rslt1 = arityImpl_734(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_340(empty_list, rslt1);
List *varArgs3 = empty_list;
incRef((Value *)arg2);
varArgs3 = (List *)listCons((Value *)arg2, varArgs3);
Value *rslt4 = arityImpl_238(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_348(empty_list, rslt1);
Value *rslt6 = protoFnImpl_345(empty_list, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
incRef((Value *)rslt2);
varArgs7 = (List *)listCons((Value *)rslt2, varArgs7);
Value *rslt8 = arityImpl_371(empty_list, (Value *)varArgs7);
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
Function fn_736 = {3, -1, "replace-at-nth", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_737}}};


// --------- remove-nth --------------
Function fn_739;
Value *arityImpl_740(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt7 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt8 = protoFnImpl_316(empty_list, arg0);
Value *rslt9 = arityImpl_556(empty_list, rslt8);
Value *rslt10 = arityImpl_408(empty_list, rslt9, arg1);
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
Value *rslt1 = arityImpl_734(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_340(empty_list, rslt1);
Value *rslt3 = arityImpl_348(empty_list, rslt1);
Value *rslt4 = protoFnImpl_345(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
Value *rslt6 = arityImpl_371(empty_list, (Value *)varArgs5);
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
Function fn_739 = {3, -1, "remove-nth", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_740}}};


// --------- partition --------------
Function fn_742;
Value *arityImpl_743(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_316(empty_list, arg0);
Value *rslt6 = arityImpl_408(empty_list, rslt5, arg1);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_727(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_730(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_743(closures, rslt2, arg1);
Value *rslt4 = arityImpl_118(empty_list, rslt1, rslt3);
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
Function fn_742 = {3, -1, "partition", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_743}}};


// --------- partition-all --------------
Function fn_745;
Value *arityImpl_746(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_316(empty_list, arg0);
Value *rslt6 = arityImpl_408(empty_list, rslt5, arg1);
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
Value *rslt8 = arityImpl_238(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_727(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_730(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_746(closures, rslt2, arg1);
Value *rslt4 = arityImpl_118(empty_list, rslt1, rslt3);
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
Function fn_745 = {3, -1, "partition-all", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_746}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_52 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_748;
Value *arityImpl_749(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_300(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs6 = (List *)listCons((Value *)(Value *)&_str_52, varArgs6);
Value *rslt7 = arityImpl_284(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
Value *rslt8 = arityImpl_82(empty_list);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt9 = arityImpl_404(empty_list, arg1, (Value *)&_num_10);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_335(empty_list, arg0);
Value *rslt11 = protoFnImpl_340(empty_list, rslt10);
incRef(rslt11);
cond0 = rslt11;
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt1 = protoFnImpl_335(empty_list, arg0);
Value *rslt2 = protoFnImpl_345(empty_list, rslt1);
Value *rslt3 = arityImpl_556(empty_list, arg1);
Value *rslt4 = arityImpl_749(closures, rslt2, rslt3);
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

Value *arityImpl_750(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt6 = arityImpl_404(empty_list, arg1, (Value *)&_num_10);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_335(empty_list, arg0);
Value *rslt8 = protoFnImpl_340(empty_list, rslt7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_335(empty_list, arg0);
Value *rslt2 = protoFnImpl_345(empty_list, rslt1);
Value *rslt3 = arityImpl_556(empty_list, arg1);
Value *rslt4 = arityImpl_750(closures, rslt2, rslt3, arg2);
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
Function fn_748 = {3, -1, "nth", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_749}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_750}}};


// --------- last --------------
Function fn_752;
Value *arityImpl_753(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_316(empty_list, arg0);
Value *rslt1 = arityImpl_556(empty_list, rslt0);
Value *rslt2 = arityImpl_749(empty_list, arg0, rslt1);
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
Function fn_752 = {3, -1, "last", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_753}}};


// --------- butlast --------------
Function fn_755;
Value *arityImpl_756(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt6 = protoFnImpl_316(empty_list, arg0);
Value *rslt7 = arityImpl_404(empty_list, (Value *)&_num_1, rslt6);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_345(empty_list, arg0);
Value *rslt3 = arityImpl_756(closures, rslt2);
Value *rslt4 = arityImpl_118(empty_list, rslt1, rslt3);
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
Function fn_755 = {3, -1, "butlast", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_756}}};


// --------- map-assoc --------------
Function fn_758;
Value *arityImpl_759(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = arityImpl_267(empty_list, arg0);
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
Value *rslt7 = arityImpl_238(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
Value *rslt9 = arityImpl_238(empty_list, (Value *)varArgs8);
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
Value *rslt10 = arityImpl_124(empty_list, arg0);
Value *rslt11 = arityImpl_124(empty_list, rslt10);
Value *rslt12 = arityImpl_404(empty_list, rslt11, arg1);
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
Value *rslt14 = arityImpl_238(empty_list, (Value *)varArgs13);
decRef((Value *)varArgs13);
my_free((Value *)varArgs13);
Value *rslt15 = arityImpl_127(empty_list, arg0);
Value *rslt16 = arityImpl_118(empty_list, rslt14, rslt15);
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
Value *rslt1 = arityImpl_124(empty_list, arg0);
Value *rslt2 = arityImpl_127(empty_list, arg0);
Value *rslt3 = arityImpl_759(closures, rslt2, arg1, arg2);
Value *rslt4 = arityImpl_118(empty_list, rslt1, rslt3);
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
Function fn_758 = {3, -1, "map-assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_759}}};


// --------- map-get --------------
Function fn_761;
Value *arityImpl_762(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt3 = arityImpl_267(empty_list, arg0);
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
Value *rslt4 = arityImpl_124(empty_list, arg0);
Value *rslt5 = arityImpl_124(empty_list, rslt4);
Value *rslt6 = arityImpl_404(empty_list, rslt5, arg1);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = arityImpl_124(empty_list, arg0);
Value *rslt8 = arityImpl_127(empty_list, rslt7);
Value *rslt9 = arityImpl_124(empty_list, rslt8);
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
Value *rslt1 = arityImpl_127(empty_list, arg0);
Value *rslt2 = arityImpl_762(closures, rslt1, arg1, arg2);
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
Function fn_761 = {3, -1, "map-get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_762}}};

SubString _kw_5 = {5, -1, 6, 0, ":hm-nf"};

// --------- hash-map= --------------
Function fn_764;
Value *arityImpl_765(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt13 = protoFnImpl_300(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_340(empty_list, rslt1);
Value *rslt3 = protoFnImpl_345(empty_list, rslt1);
Value *rslt4 = protoFnImpl_340(empty_list, rslt3);
Value *cond5;
Value *rslt8 = arityImpl_404(empty_list, (Value *)&_kw_5, rslt2);
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
Value *rslt9 = arityImpl_404(empty_list, (Value *)&_kw_5, rslt4);
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
Value *rslt10 = protoFnImpl_382(empty_list, arg1, rslt2, (Value *)&_kw_5);
Value *rslt11 = arityImpl_404(empty_list, rslt4, rslt10);
Value *rslt12 = arityImpl_395(empty_list, rslt11);
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
Value *rslt6 = protoFnImpl_345(empty_list, arg0);
Value *rslt7 = arityImpl_765(closures, rslt6, arg1);
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
Function fn_764 = {3, -1, "hash-map=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_765}}};

ProtoImpls *protoImpls_767;
Value *protoFnImpl_770(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_767);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '.a-list' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
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
FnArity protoFnArity_771 = {8, -1, 1, (List *)0, 0, protoFnImpl_770};
Function protoFn_768 = {3, -1, ".a-list", 1, {&protoFnArity_771}};

// forward declaration for 'HashMap'
Value *var_772;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_53 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_54 = {1, -1, 1,"{"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_55 = {1, -1, 1,"}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_56 = {1, -1, 7,"HashMap"};
Number _num_13 = {2, -1, 17};

// --------- instance?_impl --------------
Function fn_773;
Value *arityImpl_774(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_85(empty_list, arg1);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_13, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_773 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_774}}};

Value *protoImpl_775(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_776 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_775}}};


// --------- invoke_impl --------------
Function fn_777;

// --------- seq_impl --------------
Function fn_779;
Value *arityImpl_780(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_781(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_782 = {3, -1, "seq", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_781}}};


// --------- first_impl --------------
Function fn_783;
Value *arityImpl_784(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_124(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_785(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_786 = {3, -1, "first", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_785}}};


// --------- rest_impl --------------
Function fn_787;
Value *arityImpl_788(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_127(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_789(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_790 = {3, -1, "rest", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_789}}};


// --------- =*_impl --------------
Function fn_791;
Value *arityImpl_792(List *closures, Value *arg0, Value *arg1) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt3 = protoFnImpl_316(empty_list, val1);
Value *rslt4 = protoFnImpl_335(empty_list, arg1);
Value *rslt5 = protoFnImpl_316(empty_list, rslt4);
Value *rslt6 = arityImpl_404(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_395(empty_list, rslt6);
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
Value *rslt2 = arityImpl_765(empty_list, val1, arg1);
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

Value *protoImpl_793(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_794 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_793}}};


// --------- string-list_impl --------------
Function fn_795;

// --------- anon --------------
Function fn_797;
Value *arityImpl_798(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_246(empty_list, arg0, (Value *)&protoFn_255);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_35);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_35, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_270(empty_list, rslt0, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_370);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_370, varArgs4);
Value *rslt5 = arityImpl_232(empty_list, (Value *)varArgs4);
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
Function fn_797 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_798}}};

Value *arityImpl_796(List *closures, Value *arg0) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt15 = arityImpl_267(empty_list, val1);
decRef(rslt15);
my_free(rslt15);

if (isTrue(rslt15)) {
decRef(rslt15);
my_free(rslt15);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_53);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_53, varArgs16);
Value *rslt17 = arityImpl_238(empty_list, (Value *)varArgs16);
decRef((Value *)varArgs16);
my_free((Value *)varArgs16);
incRef(rslt17);
cond0 = rslt17;
decRef(rslt17);
my_free(rslt17);
} else {
decRef(rslt15);
my_free(rslt15);
Value *rslt3 = protoFnImpl_246(empty_list, val1, (Value *)&fn_797);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_46, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = arityImpl_270(empty_list, rslt3, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)(Value *)&fn_370);
varArgs7 = (List *)listCons((Value *)(Value *)&fn_370, varArgs7);
Value *rslt8 = arityImpl_232(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&_str_54);
varArgs9 = (List *)listCons((Value *)(Value *)&_str_54, varArgs9);
Value *rslt10 = arityImpl_238(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_55);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_55, varArgs11);
Value *rslt12 = arityImpl_238(empty_list, (Value *)varArgs11);
decRef((Value *)varArgs11);
my_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)rslt12);
varArgs13 = (List *)listCons((Value *)rslt12, varArgs13);
incRef((Value *)rslt8);
varArgs13 = (List *)listCons((Value *)rslt8, varArgs13);
incRef((Value *)rslt10);
varArgs13 = (List *)listCons((Value *)rslt10, varArgs13);
Value *rslt14 = arityImpl_371(empty_list, (Value *)varArgs13);
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

Value *protoImpl_799(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_800 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_799}}};


// --------- empty?_impl --------------
Function fn_801;
Value *arityImpl_802(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_300(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_803(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_804 = {3, -1, "empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_803}}};


// --------- count_impl --------------
Function fn_805;
Value *arityImpl_806(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_316(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_807(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_808 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_807}}};


// --------- zero_impl --------------
Function fn_809;
Value *arityImpl_810(List *closures, Value *arg0) {
Value *rslt3;
if((var_772)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_772, var_115);
} else {
FnArity *arity0 = findFnArity(var_772, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, var_115);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_115);
varArgs1 = (List *)listCons(var_115, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_772)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- zero_impl main body --------------
Function fn_809 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_810}}};

Value *protoImpl_811(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_812 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_811}}};


// --------- comp*_impl --------------
Function fn_813;

// --------- anon --------------
Function fn_815;

// --------- anon --------------
Function fn_817;
Value *arityImpl_818(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_749(empty_list, arg1, (Value *)&_num_10);
Value *rslt1 = arityImpl_749(empty_list, arg1, (Value *)&_num_1);
Value *rslt2 = protoFnImpl_376(empty_list, arg0, rslt0, rslt1);
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
Function fn_817 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_818}}};

Value *arityImpl_816(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_335(empty_list, arg1);
Value *rslt2 = arityImpl_418(empty_list, rslt0, arg0, (Value *)&fn_817);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_815 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_816}}};

Value *arityImpl_814(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg1);
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
Value *rslt2 = arityImpl_418(empty_list, arg1, arg0, (Value *)&fn_815);
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
Function fn_813 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_814}}};

Value *protoImpl_819(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_820 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_819}}};


// --------- assoc_impl --------------
Function fn_821;
Value *arityImpl_822(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_759(empty_list, val0, arg1, arg2);
Value *rslt5;
if((var_772)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, var_772, rslt1);
} else {
FnArity *arity2 = findFnArity(var_772, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_772)->name);
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

Value *protoImpl_823(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_824 = {3, -1, "assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_823}}};


// --------- get_impl --------------
Function fn_825;
Value *arityImpl_826(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_762(empty_list, val0, arg1, arg2);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_827(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_828 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_827}}};


// --------- keys_impl --------------
Function fn_829;
Value *arityImpl_830(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_246(empty_list, val0, (Value *)&protoFn_338);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_831(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[11])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_832 = {3, -1, "keys", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_831}}};


// --------- vals_impl --------------
Function fn_833;
Value *arityImpl_834(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_246(empty_list, val0, (Value *)&fn_347);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_835(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[12])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_836 = {3, -1, "vals", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_835}}};


// --------- type-name_impl --------------
Function fn_837;
Value *arityImpl_838(List *closures, Value *arg0) {
incRef((Value *)&_str_56);
return((Value *)&_str_56);
};


// --------- type-name_impl main body --------------
Function fn_837 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_838}}};

Value *protoImpl_839(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[13])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_840 = {3, -1, "type-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_839}}};


// --------- .a-list_impl --------------
Function fn_841;
Value *arityImpl_842(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_843(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[14])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_844 = {3, -1, ".a-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_843}}};

Value *arityImpl_778(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_780;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_779 = malloc_function(1);
fn_779->type = 3;
fn_779->name = "seq_impl";
fn_779->arityCount = 1;
fn_779->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_784;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_783 = malloc_function(1);
fn_783->type = 3;
fn_783->name = "first_impl";
fn_783->arityCount = 1;
fn_783->arities[0] = arity_1;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = 8;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_788;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_787 = malloc_function(1);
fn_787->type = 3;
fn_787->name = "rest_impl";
fn_787->arityCount = 1;
fn_787->arities[0] = arity_2;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_792;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_791 = malloc_function(1);
fn_791->type = 3;
fn_791->name = "=*_impl";
fn_791->arityCount = 1;
fn_791->arities[0] = arity_3;
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 1;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_796;
incRef((Value *)arg1);
arity_4->closures = listCons((Value *)arg1, (List *)arity_4->closures);
Function *fn_795 = malloc_function(1);
fn_795->type = 3;
fn_795->name = "string-list_impl";
fn_795->arityCount = 1;
fn_795->arities[0] = arity_4;
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_802;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_801 = malloc_function(1);
fn_801->type = 3;
fn_801->name = "empty?_impl";
fn_801->arityCount = 1;
fn_801->arities[0] = arity_5;
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_806;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_805 = malloc_function(1);
fn_805->type = 3;
fn_805->name = "count_impl";
fn_805->arityCount = 1;
fn_805->arities[0] = arity_6;
FnArity *arity_9 = malloc_fnArity();
arity_9->type = 8;
arity_9->count = 3;
arity_9->closures = empty_list;
arity_9->variadic = 0;
arity_9->fn = arityImpl_822;
incRef((Value *)arg1);
arity_9->closures = listCons((Value *)arg1, (List *)arity_9->closures);
Function *fn_821 = malloc_function(1);
fn_821->type = 3;
fn_821->name = "assoc_impl";
fn_821->arityCount = 1;
fn_821->arities[0] = arity_9;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = 8;
arity_10->count = 3;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_826;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_825 = malloc_function(1);
fn_825->type = 3;
fn_825->name = "get_impl";
fn_825->arityCount = 1;
fn_825->arities[0] = arity_10;
FnArity *arity_11 = malloc_fnArity();
arity_11->type = 8;
arity_11->count = 1;
arity_11->closures = empty_list;
arity_11->variadic = 0;
arity_11->fn = arityImpl_830;
incRef((Value *)arg1);
arity_11->closures = listCons((Value *)arg1, (List *)arity_11->closures);
Function *fn_829 = malloc_function(1);
fn_829->type = 3;
fn_829->name = "keys_impl";
fn_829->arityCount = 1;
fn_829->arities[0] = arity_11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = 8;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_834;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_833 = malloc_function(1);
fn_833->type = 3;
fn_833->name = "vals_impl";
fn_833->arityCount = 1;
fn_833->arities[0] = arity_12;
FnArity *arity_14 = malloc_fnArity();
arity_14->type = 8;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_842;
incRef((Value *)arg1);
arity_14->closures = listCons((Value *)arg1, (List *)arity_14->closures);
Function *fn_841 = malloc_function(1);
fn_841->type = 3;
fn_841->name = ".a-list_impl";
fn_841->arityCount = 1;
fn_841->arities[0] = arity_14;
Value *reified_15 = (Value *)malloc_reified(15);
((ReifiedVal *)reified_15)->type = 17;
((ReifiedVal *)reified_15)->implCount = 15;
((ReifiedVal *)reified_15)->impls[0] = (Value *)fn_779;
incRef((Value *)fn_779);
((ReifiedVal *)reified_15)->impls[1] = (Value *)fn_783;
incRef((Value *)fn_783);
((ReifiedVal *)reified_15)->impls[2] = (Value *)fn_787;
incRef((Value *)fn_787);
((ReifiedVal *)reified_15)->impls[3] = (Value *)fn_791;
incRef((Value *)fn_791);
((ReifiedVal *)reified_15)->impls[4] = (Value *)fn_795;
incRef((Value *)fn_795);
((ReifiedVal *)reified_15)->impls[5] = (Value *)fn_801;
incRef((Value *)fn_801);
((ReifiedVal *)reified_15)->impls[6] = (Value *)fn_805;
incRef((Value *)fn_805);
((ReifiedVal *)reified_15)->impls[7] = (Value *)&fn_809;
incRef((Value *)&fn_809);
((ReifiedVal *)reified_15)->impls[8] = (Value *)&fn_813;
incRef((Value *)&fn_813);
((ReifiedVal *)reified_15)->impls[9] = (Value *)fn_821;
incRef((Value *)fn_821);
((ReifiedVal *)reified_15)->impls[10] = (Value *)fn_825;
incRef((Value *)fn_825);
((ReifiedVal *)reified_15)->impls[11] = (Value *)fn_829;
incRef((Value *)fn_829);
((ReifiedVal *)reified_15)->impls[12] = (Value *)fn_833;
incRef((Value *)fn_833);
((ReifiedVal *)reified_15)->impls[13] = (Value *)&fn_837;
incRef((Value *)&fn_837);
((ReifiedVal *)reified_15)->impls[14] = (Value *)fn_841;
incRef((Value *)fn_841);
incRef(reified_15);
decRef((Value *)fn_779);
my_free((Value *)fn_779);
decRef((Value *)fn_783);
my_free((Value *)fn_783);
decRef((Value *)fn_787);
my_free((Value *)fn_787);
decRef((Value *)fn_791);
my_free((Value *)fn_791);
decRef((Value *)fn_795);
my_free((Value *)fn_795);
decRef((Value *)fn_801);
my_free((Value *)fn_801);
decRef((Value *)fn_805);
my_free((Value *)fn_805);
decRef((Value *)fn_821);
my_free((Value *)fn_821);
decRef((Value *)fn_825);
my_free((Value *)fn_825);
decRef((Value *)fn_829);
my_free((Value *)fn_829);
decRef((Value *)fn_833);
my_free((Value *)fn_833);
decRef((Value *)fn_841);
my_free((Value *)fn_841);
decRef(reified_15);
my_free(reified_15);
return(reified_15);
};


// --------- invoke_impl main body --------------
Function fn_777 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_778}}};

Value *protoImpl_845(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_846 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_845}}};

ReifiedVal reified_847 = {16, -1, 2, {(Value *)&fn_773, (Value *)&fn_777}};
Value *var_772 = (Value *)&reified_847;

// --------- hash-map --------------
Function fn_848;
Value *arityImpl_849(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_743(empty_list, arg0, (Value *)&_num_2);
Value *rslt4;
if((var_772)->type != 3) {
rslt4 = protoFnImpl_10(empty_list, var_772, rslt0);
} else {
FnArity *arity1 = findFnArity(var_772, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_772)->name);
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
Function fn_848 = {3, -1, "hash-map", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_849}}};

SubString _kw_6 = {5, -1, 10, 0, ":not-found"};

// --------- merge-with --------------
Function fn_851;

// --------- anon --------------
Function fn_853;

// --------- anon --------------
Function fn_855;
Value *arityImpl_856(List *closures, Value *arg0, Value *arg1) {
Value *val5 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt13 = protoFnImpl_316(empty_list, arg1);
Value *rslt14 = arityImpl_404(empty_list, (Value *)&_num_2, rslt13);
Value *rslt15 = arityImpl_395(empty_list, rslt14);
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
Value *rslt1 = arityImpl_749(empty_list, arg1, (Value *)&_num_10);
Value *rslt2 = arityImpl_749(empty_list, arg1, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_382(empty_list, arg0, rslt1, (Value *)&_kw_6);
Value *cond4;
Value *rslt11 = arityImpl_404(empty_list, (Value *)&_kw_6, rslt3);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_376(empty_list, arg0, rslt1, rslt2);
incRef(rslt12);
cond4 = rslt12;
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt11);
my_free(rslt11);
Value *rslt9;
if((val5)->type != 3) {
rslt9 = protoFnImpl_12(empty_list, val5, rslt3, rslt2);
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
Value *rslt10 = protoFnImpl_376(empty_list, arg0, rslt1, rslt9);
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

Value *arityImpl_854(List *closures, Value *arg0, Value *arg1) {
Value *val2 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt0 = protoFnImpl_335(empty_list, arg1);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_856;
incRef((Value *)val2);
arity_1->closures = listCons((Value *)val2, (List *)arity_1->closures);
Function *fn_855 = malloc_function(1);
fn_855->type = 3;
fn_855->name = "anon";
fn_855->arityCount = 1;
fn_855->arities[0] = arity_1;
Value *rslt3 = arityImpl_418(empty_list, rslt0, arg0, (Value *)fn_855);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef((Value *)fn_855);
my_free((Value *)fn_855);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *arityImpl_852(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_300(empty_list, arg2);
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
arity_1->fn = arityImpl_854;
incRef((Value *)arg0);
arity_1->closures = listCons((Value *)arg0, (List *)arity_1->closures);
Function *fn_853 = malloc_function(1);
fn_853->type = 3;
fn_853->name = "anon";
fn_853->arityCount = 1;
fn_853->arities[0] = arity_1;
Value *rslt2 = arityImpl_418(empty_list, arg2, arg1, (Value *)fn_853);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_853);
my_free((Value *)fn_853);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- merge-with main body --------------
Function fn_851 = {3, -1, "merge-with", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_852}}};

SubString _kw_7 = {5, -1, 17, 0, ":get-in-not-found"};

// --------- get-in --------------
Function fn_858;
Value *arityImpl_859(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt7 = protoFnImpl_316(empty_list, arg1);
Value *rslt8 = arityImpl_404(empty_list, rslt7, (Value *)&_num_10);
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
Value *rslt9 = protoFnImpl_316(empty_list, arg1);
Value *rslt10 = arityImpl_404(empty_list, rslt9, (Value *)&_num_1);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
Value *rslt11 = protoFnImpl_340(empty_list, arg1);
Value *rslt12 = protoFnImpl_382(empty_list, arg0, rslt11, arg2);
incRef(rslt12);
cond0 = rslt12;
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_382(empty_list, arg0, rslt1, (Value *)&_kw_7);
Value *cond3;
Value *rslt6 = arityImpl_404(empty_list, (Value *)&_kw_7, rslt2);
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
Value *rslt4 = protoFnImpl_345(empty_list, arg1);
Value *rslt5 = arityImpl_859(closures, rslt2, rslt4, arg2);
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
Function fn_858 = {3, -1, "get-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_859}}};

SubString _kw_8 = {5, -1, 14, 0, ":update-in-nil"};

// --------- update-in --------------
Function fn_861;
Value *arityImpl_862(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt8 = protoFnImpl_316(empty_list, arg1);
Value *rslt9 = arityImpl_404(empty_list, rslt8, (Value *)&_num_10);
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
Value *rslt10 = protoFnImpl_316(empty_list, arg1);
Value *rslt11 = arityImpl_404(empty_list, rslt10, (Value *)&_num_1);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_340(empty_list, arg1);
Value *rslt13 = protoFnImpl_382(empty_list, arg0, rslt12, (Value *)&_kw_8);
Value *cond14;
Value *rslt20 = arityImpl_404(empty_list, (Value *)&_kw_8, rslt13);
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
rslt18 = protoFnImpl_10(empty_list, arg2, rslt13);
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
Value *rslt19 = protoFnImpl_376(empty_list, arg0, rslt12, rslt18);
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
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_382(empty_list, arg0, rslt1, (Value *)&_kw_8);
Value *cond3;
Value *rslt7 = arityImpl_404(empty_list, (Value *)&_kw_8, rslt2);
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
Value *rslt4 = protoFnImpl_345(empty_list, arg1);
Value *rslt5 = arityImpl_862(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_376(empty_list, arg0, rslt1, rslt5);
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
Function fn_861 = {3, -1, "update-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_862}}};

SubString _kw_9 = {5, -1, 13, 0, ":assoc-in-nil"};

// --------- assoc-in --------------
Function fn_864;
Value *arityImpl_865(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt13 = protoFnImpl_316(empty_list, arg1);
Value *rslt14 = arityImpl_404(empty_list, rslt13, (Value *)&_num_10);
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
Value *rslt15 = protoFnImpl_316(empty_list, arg1);
Value *rslt16 = arityImpl_404(empty_list, rslt15, (Value *)&_num_1);
decRef(rslt15);
my_free(rslt15);
decRef(rslt16);
my_free(rslt16);

if (isTrue(rslt16)) {
decRef(rslt16);
my_free(rslt16);
Value *rslt17 = protoFnImpl_340(empty_list, arg1);
Value *rslt18 = protoFnImpl_376(empty_list, arg0, rslt17, arg2);
incRef(rslt18);
cond0 = rslt18;
decRef(rslt17);
my_free(rslt17);
decRef(rslt18);
my_free(rslt18);
} else {
decRef(rslt16);
my_free(rslt16);
Value *rslt1 = protoFnImpl_340(empty_list, arg1);
Value *rslt2 = protoFnImpl_382(empty_list, arg0, rslt1, (Value *)&_kw_9);
Value *cond3;
Value *rslt7 = arityImpl_404(empty_list, (Value *)&_kw_9, rslt2);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
List *varArgs8 = empty_list;
Value *rslt9 = arityImpl_849(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_345(empty_list, arg1);
Value *rslt11 = arityImpl_865(closures, rslt9, rslt10, arg2);
Value *rslt12 = protoFnImpl_376(empty_list, arg0, rslt1, rslt11);
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
Value *rslt4 = protoFnImpl_345(empty_list, arg1);
Value *rslt5 = arityImpl_865(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_376(empty_list, arg0, rslt1, rslt5);
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
Function fn_864 = {3, -1, "assoc-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_865}}};


// --------- =*_impl --------------
Function fn_867;
Value *arityImpl_868(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt1 = arityImpl_85(empty_list, arg1);
Value *rslt2 = arityImpl_404(empty_list, rslt0, rslt1);
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
Function fn_867 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_868}}};

Value *protoImpl_869(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_870 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_869}}};

ReifiedVal reified_871 = {18, -1, 1, {(Value *)&fn_867}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[19];} _str_57 = {1, -1, 18,"Could not look up "};

// --------- =*_impl --------------
Function fn_873;
Value *arityImpl_874(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_142(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_873 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_874}}};


// --------- name_impl --------------
Function fn_875;
Value *arityImpl_876(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_70(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_875 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_876}}};


// --------- string-list_impl --------------
Function fn_877;
Value *arityImpl_878(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_252(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
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
Function fn_877 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_878}}};


// --------- invoke_impl --------------
Function fn_879;
Value *arityImpl_880(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_382(empty_list, arg1, arg0, (Value *)&reified_871);
Value *cond1;
Value *rslt2 = arityImpl_404(empty_list, (Value *)&reified_871, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_57);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_57, varArgs3);
Value *rslt4 = arityImpl_284(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_82(empty_list);
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
Function fn_879 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_880}}};


// --------- =*_impl --------------
Function fn_881;
Value *arityImpl_882(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_142(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_881 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_882}}};


// --------- name_impl --------------
Function fn_883;
Value *arityImpl_884(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_70(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_883 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_884}}};


// --------- string-list_impl --------------
Function fn_885;
Value *arityImpl_886(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_252(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
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
Function fn_885 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_886}}};


// --------- invoke_impl --------------
Function fn_887;
Value *arityImpl_888(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_382(empty_list, arg1, arg0, (Value *)&reified_871);
Value *cond1;
Value *rslt2 = arityImpl_404(empty_list, (Value *)&reified_871, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_57);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_57, varArgs3);
Value *rslt4 = arityImpl_284(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_82(empty_list);
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
Function fn_887 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_888}}};


// --------- invoke_impl --------------
Function fn_889;
Value *arityImpl_890(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_382(empty_list, arg1, arg0, arg2);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- invoke_impl main body --------------
Function fn_889 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_890}}};


// --------- symbol? --------------
Function fn_891;
Value *arityImpl_892(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_7, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- symbol? main body --------------
Function fn_891 = {3, -1, "symbol?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_892}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_58 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_894;
Value *arityImpl_895(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_58);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_58, varArgs0);
Value *rslt1 = arityImpl_720(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_79(empty_list, rslt1);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- keyword main body --------------
Function fn_894 = {3, -1, "keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_895}}};


// --------- keyword? --------------
Function fn_897;
Value *arityImpl_898(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_5, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- keyword? main body --------------
Function fn_897 = {3, -1, "keyword?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_898}}};


// --------- number? --------------
Function fn_900;
Value *arityImpl_901(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_2, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- number? main body --------------
Function fn_900 = {3, -1, "number?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_901}}};


// --------- string? --------------
Function fn_903;
Value *arityImpl_904(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_85(empty_list, arg0);
Value *rslt1 = arityImpl_404(empty_list, (Value *)&_num_1, rslt0);
Value *rslt2 = arityImpl_85(empty_list, arg0);
Value *rslt3 = arityImpl_404(empty_list, (Value *)&_num_6, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)rslt1);
varArgs4 = (List *)listCons((Value *)rslt1, varArgs4);
Value *rslt5 = arityImpl_401(empty_list, (Value *)varArgs4);
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
Function fn_903 = {3, -1, "string?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_904}}};


// --------- range* --------------
Function fn_906;
Value *arityImpl_907(List *closures, Value *arg0) {
Value *cond0;
Value *rslt4 = arityImpl_404(empty_list, (Value *)&_num_10, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_num_10);
varArgs5 = (List *)listCons((Value *)(Value *)&_num_10, varArgs5);
Value *rslt6 = arityImpl_238(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = arityImpl_556(empty_list, arg0);
Value *rslt2 = arityImpl_907(closures, rslt1);
Value *rslt3 = arityImpl_118(empty_list, arg0, rslt2);
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
Function fn_906 = {3, -1, "range*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_907}}};


// --------- range --------------
Function fn_909;
Value *arityImpl_910(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_556(empty_list, arg0);
Value *rslt1 = arityImpl_907(empty_list, rslt0);
Value *rslt2 = arityImpl_429(empty_list, rslt1);
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
Function fn_909 = {3, -1, "range", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_910}}};


// --------- repeat --------------
Function fn_912;

// --------- anon --------------
Function fn_914;
Value *arityImpl_915(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *arityImpl_913(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_408(empty_list, arg0, (Value *)&_num_1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_115);
cond0 = var_115;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_556(empty_list, arg0);
Value *rslt2 = arityImpl_907(empty_list, rslt1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_915;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_914 = malloc_function(1);
fn_914->type = 3;
fn_914->name = "anon";
fn_914->arityCount = 1;
fn_914->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_246(empty_list, rslt2, (Value *)fn_914);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_914);
my_free((Value *)fn_914);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- repeat main body --------------
Function fn_912 = {3, -1, "repeat", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_913}}};

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
numInfo = listCons(numberValue(14), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_13"), empty_list);
numInfo = listCons(numberValue(17), numInfo);
nums = listCons((Value *)numInfo, nums);
return((Value *)nums);
}

Value *string_literals() {
List *strs = empty_list;
List *strInfo;
strInfo = listCons(stringValue("_str_0"), empty_list);
strInfo = listCons(stringValue("String"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_1"), empty_list);
strInfo = listCons(stringValue("Number"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_2"), empty_list);
strInfo = listCons(stringValue("Function"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_3"), empty_list);
strInfo = listCons(stringValue("List"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_4"), empty_list);
strInfo = listCons(stringValue("Keyword"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_5"), empty_list);
strInfo = listCons(stringValue("SubStr"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_6"), empty_list);
strInfo = listCons(stringValue("Symbol"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_7"), empty_list);
strInfo = listCons(stringValue("FnArity"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_8"), empty_list);
strInfo = listCons(stringValue("Opaque"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_9"), empty_list);
strInfo = listCons(stringValue("void"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_10"), empty_list);
strInfo = listCons(stringValue("char"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_11"), empty_list);
strInfo = listCons(stringValue("char *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_12"), empty_list);
strInfo = listCons(stringValue("int"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_13"), empty_list);
strInfo = listCons(stringValue("int64_t"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_14"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs;} Value;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_15"), empty_list);
strInfo = listCons(stringValue("Value *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_16"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_17"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_18"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_19"), empty_list);
strInfo = listCons(stringValue("typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_20"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_21"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_22"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_23"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_24"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_25"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_26"), empty_list);
strInfo = listCons(stringValue(":match*-one-arg"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_27"), empty_list);
strInfo = listCons(stringValue(":match*-two-args"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_28"), empty_list);
strInfo = listCons(stringValue("*** call to 'instance?' with unknown type parameter."), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_29"), empty_list);
strInfo = listCons(stringValue("'flat-map' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_30"), empty_list);
strInfo = listCons(stringValue("'duplicate' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_31"), empty_list);
strInfo = listCons(stringValue("*** 'wrap' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_32"), empty_list);
strInfo = listCons(stringValue("'name' not implemented for type "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_33"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_34"), empty_list);
strInfo = listCons(stringValue("'serialize' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_35"), empty_list);
strInfo = listCons(stringValue(" "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_36"), empty_list);
strInfo = listCons(stringValue("\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_37"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_38"), empty_list);
strInfo = listCons(stringValue("'=*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue("'<*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_40"), empty_list);
strInfo = listCons(stringValue("'count' not implemented for "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
strInfo = listCons(stringValue("'get' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_42"), empty_list);
strInfo = listCons(stringValue("<Fn: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_43"), empty_list);
strInfo = listCons(stringValue(">"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_44"), empty_list);
strInfo = listCons(stringValue("ZipList"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_45"), empty_list);
strInfo = listCons(stringValue("("), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_46"), empty_list);
strInfo = listCons(stringValue(", "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_47"), empty_list);
strInfo = listCons(stringValue(")"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_48"), empty_list);
strInfo = listCons(stringValue("<nothing>"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_49"), empty_list);
strInfo = listCons(stringValue("<maybe "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_50"), empty_list);
strInfo = listCons(stringValue("maybe-val"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_51"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_52"), empty_list);
strInfo = listCons(stringValue("'nth' from empty seq"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_53"), empty_list);
strInfo = listCons(stringValue("{}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_54"), empty_list);
strInfo = listCons(stringValue("{"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_55"), empty_list);
strInfo = listCons(stringValue("}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_56"), empty_list);
strInfo = listCons(stringValue("HashMap"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_57"), empty_list);
strInfo = listCons(stringValue("Could not look up "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_58"), empty_list);
strInfo = listCons(stringValue(":"), strInfo);
strs = listCons((Value *)strInfo, strs);
return((Value *)strs);
}

Value *keyword_literals() {
List *kws = empty_list;
List *kwInfo;
kwInfo = listCons(stringValue("_kw_0"), empty_list);
kwInfo = listCons(keywordValue(":x"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_1"), empty_list);
kwInfo = listCons(keywordValue(":m"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_2"), empty_list);
kwInfo = listCons(keywordValue(":k"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_3"), empty_list);
kwInfo = listCons(keywordValue(":nil"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_4"), empty_list);
kwInfo = listCons(keywordValue(":nothing-here"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_5"), empty_list);
kwInfo = listCons(keywordValue(":hm-nf"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_6"), empty_list);
kwInfo = listCons(keywordValue(":not-found"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_7"), empty_list);
kwInfo = listCons(keywordValue(":get-in-not-found"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_8"), empty_list);
kwInfo = listCons(keywordValue(":update-in-nil"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_9"), empty_list);
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
impl = listCons(stringValue("(Value *)&fn_24"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_26"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_28"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_30"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_32"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_34"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_36"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_38"), impl);
impl = listCons(numberValue(8), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_40"), impl);
impl = listCons(numberValue(9), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_476"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_645"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_840"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("type-name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_1;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_0"), protoInfo);
protoInfo = listCons(stringValue("Getter/type-name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_482"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_651"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_656"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_846"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_879"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_889"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("invoke"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_6;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_5"), protoInfo);
protoInfo = listCons(stringValue("Function/invoke"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("bippity"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_166;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_165"), protoInfo);
protoInfo = listCons(stringValue("core/Variant/bippity"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_172"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("match*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_171;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_170"), protoInfo);
protoInfo = listCons(stringValue("core/Variant/match*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_180"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_464"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_603"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_660"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_776"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("instance?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_179;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_178"), protoInfo);
protoInfo = listCons(stringValue("core/Type/instance?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_186"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_541"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_597"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_641"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flat-map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_185;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_184"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flat-map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_192"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_593"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_637"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flatten"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_191;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_190"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flatten"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extract"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_199;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_198"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extract"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extend"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_204;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_203"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extend"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_210"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("duplicate"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_209;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_208"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/duplicate"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_217"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_539"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_585"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_629"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("wrap"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_216;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_215"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/wrap"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_223"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_444"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_472"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_589"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_633"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("apply*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_222;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_221"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_242"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_537"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_581"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_625"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_241;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_240"), protoInfo);
protoInfo = listCons(stringValue("core/Functor/map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_250"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_875"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_883"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_249;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_248"), protoInfo);
protoInfo = listCons(stringValue("core/Named/name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_256"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_434"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_450"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_515"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_565"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_609"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_687"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_695"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_800"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_877"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_885"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("string-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_255;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_254"), protoInfo);
protoInfo = listCons(stringValue("core/Stringable/string-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_262"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("serialize"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_261;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_260"), protoInfo);
protoInfo = listCons(stringValue("core/Serializable/serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_287"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_446"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_513"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_569"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_613"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_671"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_697"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_794"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_870"), impl);
impl = listCons(numberValue(18), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_873"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_881"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("=*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_286;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_285"), protoInfo);
protoInfo = listCons(stringValue("core/Eq/=*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_293"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_448"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("<*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_292;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_291"), protoInfo);
protoInfo = listCons(stringValue("core/Ord/<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_517"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_673"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_699"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_804"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_298;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_297"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_519"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_675"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_701"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_303;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_302"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("destruct"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_308;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_307"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/destruct"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_314"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_523"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_677"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_703"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_808"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("count"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_313;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_312"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/count"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_521"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_679"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_705"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("conj"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_319;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_318"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/conj"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_328"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_525"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_327;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_326"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_527"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_681"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_707"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_782"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_333;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_332"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_529"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_683"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_709"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_786"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_338;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_337"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_531"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_685"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_711"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_790"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("rest"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_343;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_342"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_511"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("traverse"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_351;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_350"), protoInfo);
protoInfo = listCons(stringValue("core/Traversable/traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_507"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("crush"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_356;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_355"), protoInfo);
protoInfo = listCons(stringValue("core/Crushable/crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_436"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_533"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_573"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_617"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_664"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_812"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("zero"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_361;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_360"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_438"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_535"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_577"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_621"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_668"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_689"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_713"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_820"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("comp*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_366;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_365"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/comp*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_824"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_374;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_373"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_380"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_828"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_379;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_378"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_832"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("keys"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_385;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_384"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_836"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("vals"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_390;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_389"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_480"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_649"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".v"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_456;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_455"), protoInfo);
protoInfo = listCons(stringValue("Getter/.v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_844"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".a-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_768;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_767"), protoInfo);
protoInfo = listCons(stringValue("Getter/.a-list"), protoInfo);
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
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_1"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_8"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_10"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_12"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_14"), empty_list);
arityInfo = listCons(numberValue(4), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_16"), empty_list);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_18"), empty_list);
arityInfo = listCons(numberValue(6), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_20"), empty_list);
arityInfo = listCons(numberValue(7), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_22"), empty_list);
arityInfo = listCons(numberValue(8), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_6"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_25"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_24"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_27"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_26"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_29"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_28"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_31"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_30"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_33"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_32"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_35"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_34"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_37"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_36"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_39"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_38"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_41"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_40"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_64"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_63"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_67"), empty_list);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_66"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_70"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_69"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_73"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_72"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_76"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_75"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_79"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_78"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_82"), empty_list);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_81"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_85"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_84"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_88"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_87"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_91"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_92"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_90"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_95"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_94"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_98"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_97"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_101"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_100"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_104"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_103"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_107"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_106"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_110"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_109"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_113"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_112"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_117"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_118"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_116"), fnInfo);
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
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_138"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_142"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_141"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_145"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_144"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_148"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_147"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_151"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_150"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_154"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_153"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_157"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_156"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_160"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_159"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_163"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_162"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_168"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_166"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_174"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_176"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_171"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_182"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_179"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_188"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_185"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_195"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_194"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_196"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_191"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_201"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_199"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_206"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_204"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_212"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_209"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_219"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_216"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_229"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_222"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_232"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_231"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_235"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_234"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_238"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_237"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_246"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_241"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_252"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_249"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_258"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_255"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_264"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_261"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_267"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_266"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_270"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_269"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_275"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_274"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_278"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_277"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_281"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_280"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_284"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_283"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_289"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_286"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_295"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_292"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_300"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_298"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_305"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_303"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_310"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_308"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_316"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_313"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_321"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_319"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_324"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_323"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_330"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_327"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_335"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_333"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_340"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_338"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_345"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_343"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_348"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_347"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_353"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_351"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_358"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_356"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_363"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_361"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_368"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_366"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_371"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_370"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_376"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_374"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_382"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_379"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_387"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_385"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_392"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_390"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_395"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_394"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_398"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_397"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_401"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_400"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_404"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_405"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_403"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_408"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_409"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_407"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_412"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_411"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_415"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_414"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_418"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_417"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_421"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_420"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_424"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_423"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_429"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_428"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_432"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_431"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_435"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_434"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_437"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_436"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_443"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_442"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_439"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_438"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_445"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_444"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_447"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_446"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_449"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_448"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_451"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_450"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_453"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_452"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_458"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_456"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_462"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_461"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_470"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_469"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_474"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_473"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_466"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_465"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_485"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_484"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_494"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_493"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_490"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_489"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_500"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_499"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_505"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_504"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_503"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_502"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_508"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_507"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_516"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_515"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_518"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_517"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_520"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_519"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_522"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_521"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_524"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_523"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_526"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_525"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_528"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_527"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_530"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_529"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_532"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_535"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_538"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_541"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_544"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_543"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_547"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_546"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_550"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_549"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_553"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_552"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_556"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_555"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_559"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_558"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_563"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_562"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_567"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_566"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_571"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_570"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_575"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_574"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_579"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_578"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_583"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_582"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_587"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_586"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_591"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_590"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_595"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_594"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_601"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_600"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_607"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_606"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_615"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_614"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_619"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_618"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_627"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_626"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_631"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_630"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_643"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_642"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_605"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_604"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_654"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_653"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_658"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_657"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_662"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_661"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_666"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_665"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_672"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_671"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_674"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_673"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_676"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_675"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_678"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_677"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_680"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_679"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_682"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_681"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_684"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_683"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_686"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_685"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_688"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_687"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_692"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_691"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_690"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_689"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_696"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_695"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_698"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_697"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_700"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_699"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_702"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_701"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_704"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_703"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_706"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_705"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_708"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_707"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_710"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_709"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_712"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_711"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_716"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_715"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_714"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_713"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_722"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_721"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_720"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_719"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_727"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_726"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_730"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_729"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_733"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_734"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_732"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_737"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_736"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_740"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_739"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_743"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_742"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_746"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_745"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_749"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_750"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_748"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_753"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_752"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_756"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_755"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_759"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_758"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_762"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_761"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_765"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_764"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_770"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_768"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_774"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_773"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_798"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_797"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_810"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_809"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_818"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_817"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_816"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_815"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_814"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_813"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_838"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_837"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_778"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_777"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_849"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_848"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_852"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_851"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_859"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_858"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_862"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_861"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_865"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_864"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_868"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_867"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_874"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_873"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_876"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_875"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_878"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_877"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_880"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_879"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_882"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_881"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_884"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_883"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_886"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_885"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_888"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_887"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_890"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_889"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_892"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_891"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_895"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_894"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_898"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_897"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_901"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_900"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_904"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_903"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_907"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_906"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_910"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_909"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_913"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_912"), fnInfo);
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
symInfo = listCons(symbolValue("type-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_6"), empty_list);
symInfo = listCons(stringValue("Function protoFn_6"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_837"), empty_list);
symInfo = listCons(stringValue("Function fn_837"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_283"), empty_list);
symInfo = listCons(stringValue("Function fn_283"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print-err"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_9"), empty_list);
symInfo = listCons(stringValue("String _str_9"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("VoidT"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_10"), empty_list);
symInfo = listCons(stringValue("String _str_10"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_11"), empty_list);
symInfo = listCons(stringValue("String _str_11"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_12"), empty_list);
symInfo = listCons(stringValue("String _str_12"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int32"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_13"), empty_list);
symInfo = listCons(stringValue("String _str_13"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int64"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_13"), empty_list);
symInfo = listCons(stringValue(""), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ValueType"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_14"), empty_list);
symInfo = listCons(stringValue("String _str_14"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_15"), empty_list);
symInfo = listCons(stringValue("String _str_15"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_16"), empty_list);
symInfo = listCons(stringValue("String _str_16"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("NumberVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_17"), empty_list);
symInfo = listCons(stringValue("String _str_17"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("StringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_18"), empty_list);
symInfo = listCons(stringValue("String _str_18"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("SubStringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_19"), empty_list);
symInfo = listCons(stringValue("String _str_19"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ListVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_20"), empty_list);
symInfo = listCons(stringValue("String _str_20"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArityVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_21"), empty_list);
symInfo = listCons(stringValue("String _str_21"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FunctionVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_22"), empty_list);
symInfo = listCons(stringValue("String _str_22"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_23"), empty_list);
symInfo = listCons(stringValue("String _str_23"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpls"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_24"), empty_list);
symInfo = listCons(stringValue("String _str_24"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ReifiedVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_25"), empty_list);
symInfo = listCons(stringValue("String _str_25"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("OpaqueVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_61"), empty_list);
symInfo = listCons(stringValue("Value *var_61;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("true"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_62"), empty_list);
symInfo = listCons(stringValue("Value *var_62;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("false"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_63"), empty_list);
symInfo = listCons(stringValue("Function fn_63"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("output-to-file"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_66"), empty_list);
symInfo = listCons(stringValue("Function fn_66"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("standard-output"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_69"), empty_list);
symInfo = listCons(stringValue("Function fn_69"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_72"), empty_list);
symInfo = listCons(stringValue("Function fn_72"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char-code"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_75"), empty_list);
symInfo = listCons(stringValue("Function fn_75"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_78"), empty_list);
symInfo = listCons(stringValue("Function fn_78"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("new-keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_81"), empty_list);
symInfo = listCons(stringValue("Function fn_81"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("abort"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_84"), empty_list);
symInfo = listCons(stringValue("Function fn_84"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-type"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_87"), empty_list);
symInfo = listCons(stringValue("Function fn_87"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_90"), empty_list);
symInfo = listCons(stringValue("Function fn_90"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subs"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_94"), empty_list);
symInfo = listCons(stringValue("Function fn_94"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_97"), empty_list);
symInfo = listCons(stringValue("Function fn_97"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_100"), empty_list);
symInfo = listCons(stringValue("Function fn_100"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-less-than"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_103"), empty_list);
symInfo = listCons(stringValue("Function fn_103"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("add-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_106"), empty_list);
symInfo = listCons(stringValue("Function fn_106"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subtract-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_109"), empty_list);
symInfo = listCons(stringValue("Function fn_109"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("mult-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_112"), empty_list);
symInfo = listCons(stringValue("Function fn_112"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rem"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_115"), empty_list);
symInfo = listCons(stringValue("Value *var_115;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_116"), empty_list);
symInfo = listCons(stringValue("Function fn_116"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cons"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_120"), empty_list);
symInfo = listCons(stringValue("Function fn_120"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_123"), empty_list);
symInfo = listCons(stringValue("Function fn_123"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("car"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_126"), empty_list);
symInfo = listCons(stringValue("Function fn_126"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cdr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_129"), empty_list);
symInfo = listCons(stringValue("Function fn_129"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_132"), empty_list);
symInfo = listCons(stringValue("Function fn_132"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_135"), empty_list);
symInfo = listCons(stringValue("Function fn_135"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_138"), empty_list);
symInfo = listCons(stringValue("Function fn_138"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_141"), empty_list);
symInfo = listCons(stringValue("Function fn_141"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_144"), empty_list);
symInfo = listCons(stringValue("Function fn_144"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-malloc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_147"), empty_list);
symInfo = listCons(stringValue("Function fn_147"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-append"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_150"), empty_list);
symInfo = listCons(stringValue("Function fn_150"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr-err*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_153"), empty_list);
symInfo = listCons(stringValue("Function fn_153"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("slurp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_156"), empty_list);
symInfo = listCons(stringValue("Function fn_156"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_159"), empty_list);
symInfo = listCons(stringValue("Function fn_159"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("escape-chars"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_162"), empty_list);
symInfo = listCons(stringValue("Function fn_162"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_166"), empty_list);
symInfo = listCons(stringValue("Function protoFn_166"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("bippity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_171"), empty_list);
symInfo = listCons(stringValue("Function protoFn_171"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("match*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_179"), empty_list);
symInfo = listCons(stringValue("Function protoFn_179"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_185"), empty_list);
symInfo = listCons(stringValue("Function protoFn_185"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_914"), empty_list);
symInfo = listCons(stringValue("Function fn_914"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_191"), empty_list);
symInfo = listCons(stringValue("Function protoFn_191"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_199"), empty_list);
symInfo = listCons(stringValue("Function protoFn_199"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extract"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_204"), empty_list);
symInfo = listCons(stringValue("Function protoFn_204"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_209"), empty_list);
symInfo = listCons(stringValue("Function protoFn_209"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("duplicate"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_489"), empty_list);
symInfo = listCons(stringValue("Function fn_489"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comprehend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_216"), empty_list);
symInfo = listCons(stringValue("Function protoFn_216"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_222"), empty_list);
symInfo = listCons(stringValue("Function protoFn_222"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_231"), empty_list);
symInfo = listCons(stringValue("Function fn_231"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_234"), empty_list);
symInfo = listCons(stringValue("Function fn_234"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply-to"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_237"), empty_list);
symInfo = listCons(stringValue("Function fn_237"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_241"), empty_list);
symInfo = listCons(stringValue("Function protoFn_241"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_249"), empty_list);
symInfo = listCons(stringValue("Function protoFn_249"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_255"), empty_list);
symInfo = listCons(stringValue("Function protoFn_255"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_261"), empty_list);
symInfo = listCons(stringValue("Function protoFn_261"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_266"), empty_list);
symInfo = listCons(stringValue("Function fn_266"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_269"), empty_list);
symInfo = listCons(stringValue("Function fn_269"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_274"), empty_list);
symInfo = listCons(stringValue("Function fn_274"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("prn"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_277"), empty_list);
symInfo = listCons(stringValue("Function fn_277"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_280"), empty_list);
symInfo = listCons(stringValue("Function fn_280"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_286"), empty_list);
symInfo = listCons(stringValue("Function protoFn_286"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_292"), empty_list);
symInfo = listCons(stringValue("Function protoFn_292"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_298"), empty_list);
symInfo = listCons(stringValue("Function protoFn_298"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_303"), empty_list);
symInfo = listCons(stringValue("Function protoFn_303"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_308"), empty_list);
symInfo = listCons(stringValue("Function protoFn_308"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("destruct"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_313"), empty_list);
symInfo = listCons(stringValue("Function protoFn_313"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_319"), empty_list);
symInfo = listCons(stringValue("Function protoFn_319"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_323"), empty_list);
symInfo = listCons(stringValue("Function fn_323"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_327"), empty_list);
symInfo = listCons(stringValue("Function protoFn_327"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_333"), empty_list);
symInfo = listCons(stringValue("Function protoFn_333"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_338"), empty_list);
symInfo = listCons(stringValue("Function protoFn_338"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_343"), empty_list);
symInfo = listCons(stringValue("Function protoFn_343"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_347"), empty_list);
symInfo = listCons(stringValue("Function fn_347"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("second"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_351"), empty_list);
symInfo = listCons(stringValue("Function protoFn_351"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_356"), empty_list);
symInfo = listCons(stringValue("Function protoFn_356"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_361"), empty_list);
symInfo = listCons(stringValue("Function protoFn_361"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_366"), empty_list);
symInfo = listCons(stringValue("Function protoFn_366"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_370"), empty_list);
symInfo = listCons(stringValue("Function fn_370"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_374"), empty_list);
symInfo = listCons(stringValue("Function protoFn_374"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_379"), empty_list);
symInfo = listCons(stringValue("Function protoFn_379"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_385"), empty_list);
symInfo = listCons(stringValue("Function protoFn_385"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_390"), empty_list);
symInfo = listCons(stringValue("Function protoFn_390"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_394"), empty_list);
symInfo = listCons(stringValue("Function fn_394"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_397"), empty_list);
symInfo = listCons(stringValue("Function fn_397"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("and"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_400"), empty_list);
symInfo = listCons(stringValue("Function fn_400"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("or"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_403"), empty_list);
symInfo = listCons(stringValue("Function fn_403"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_407"), empty_list);
symInfo = listCons(stringValue("Function fn_407"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_411"), empty_list);
symInfo = listCons(stringValue("Function fn_411"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_414"), empty_list);
symInfo = listCons(stringValue("Function fn_414"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_417"), empty_list);
symInfo = listCons(stringValue("Function fn_417"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_420"), empty_list);
symInfo = listCons(stringValue("Function fn_420"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("filter"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_423"), empty_list);
symInfo = listCons(stringValue("Function fn_423"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_428"), empty_list);
symInfo = listCons(stringValue("Function fn_428"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_431"), empty_list);
symInfo = listCons(stringValue("Function fn_431"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_885"), empty_list);
symInfo = listCons(stringValue("Function fn_885"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_809"), empty_list);
symInfo = listCons(stringValue("Function fn_809"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_813"), empty_list);
symInfo = listCons(stringValue("Function fn_813"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_630"), empty_list);
symInfo = listCons(stringValue("Function fn_630"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_881"), empty_list);
symInfo = listCons(stringValue("Function fn_881"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_448"), empty_list);
symInfo = listCons(stringValue("Function fn_448"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_452"), empty_list);
symInfo = listCons(stringValue("Function fn_452"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("any?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_456"), empty_list);
symInfo = listCons(stringValue("Function protoFn_456"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_460"), empty_list);
symInfo = listCons(stringValue("Value *var_460"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ZipList"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_773"), empty_list);
symInfo = listCons(stringValue("Function fn_773"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_889"), empty_list);
symInfo = listCons(stringValue("Function fn_889"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_646"), empty_list);
symInfo = listCons(stringValue("Function fn_646"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_484"), empty_list);
symInfo = listCons(stringValue("Function fn_484"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partial"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_499"), empty_list);
symInfo = listCons(stringValue("Function fn_499"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-concat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_502"), empty_list);
symInfo = listCons(stringValue("Function fn_502"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_507"), empty_list);
symInfo = listCons(stringValue("Function fn_507"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_511"), empty_list);
symInfo = listCons(stringValue("Function fn_511"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_801"), empty_list);
symInfo = listCons(stringValue("Function fn_801"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_701"), empty_list);
symInfo = listCons(stringValue("Function fn_701"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_705"), empty_list);
symInfo = listCons(stringValue("Function fn_705"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_805"), empty_list);
symInfo = listCons(stringValue("Function fn_805"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_525"), empty_list);
symInfo = listCons(stringValue("Function fn_525"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_779"), empty_list);
symInfo = listCons(stringValue("Function fn_779"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_783"), empty_list);
symInfo = listCons(stringValue("Function fn_783"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_787"), empty_list);
symInfo = listCons(stringValue("Function fn_787"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_622"), empty_list);
symInfo = listCons(stringValue("Function fn_622"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_626"), empty_list);
symInfo = listCons(stringValue("Function fn_626"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_638"), empty_list);
symInfo = listCons(stringValue("Function fn_638"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_543"), empty_list);
symInfo = listCons(stringValue("Function fn_543"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("some"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_546"), empty_list);
symInfo = listCons(stringValue("Function fn_546"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("inc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_549"), empty_list);
symInfo = listCons(stringValue("Function fn_549"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_552"), empty_list);
symInfo = listCons(stringValue("Function fn_552"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_555"), empty_list);
symInfo = listCons(stringValue("Function fn_555"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_558"), empty_list);
symInfo = listCons(stringValue("Function fn_558"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("-"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_561"), empty_list);
symInfo = listCons(stringValue("Value *var_561"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe-val"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_634"), empty_list);
symInfo = listCons(stringValue("Function fn_634"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_598"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_598"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nothing"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_669"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_669"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_719"), empty_list);
symInfo = listCons(stringValue("Function fn_719"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_726"), empty_list);
symInfo = listCons(stringValue("Function fn_726"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_729"), empty_list);
symInfo = listCons(stringValue("Function fn_729"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("drop"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_732"), empty_list);
symInfo = listCons(stringValue("Function fn_732"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_736"), empty_list);
symInfo = listCons(stringValue("Function fn_736"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("replace-at-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_739"), empty_list);
symInfo = listCons(stringValue("Function fn_739"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_742"), empty_list);
symInfo = listCons(stringValue("Function fn_742"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_745"), empty_list);
symInfo = listCons(stringValue("Function fn_745"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition-all"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_748"), empty_list);
symInfo = listCons(stringValue("Function fn_748"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_752"), empty_list);
symInfo = listCons(stringValue("Function fn_752"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("last"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_755"), empty_list);
symInfo = listCons(stringValue("Function fn_755"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_758"), empty_list);
symInfo = listCons(stringValue("Function fn_758"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_761"), empty_list);
symInfo = listCons(stringValue("Function fn_761"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_764"), empty_list);
symInfo = listCons(stringValue("Function fn_764"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_768"), empty_list);
symInfo = listCons(stringValue("Function protoFn_768"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_772"), empty_list);
symInfo = listCons(stringValue("Value *var_772"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("HashMap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_821"), empty_list);
symInfo = listCons(stringValue("Function fn_821"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_825"), empty_list);
symInfo = listCons(stringValue("Function fn_825"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_829"), empty_list);
symInfo = listCons(stringValue("Function fn_829"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_833"), empty_list);
symInfo = listCons(stringValue("Function fn_833"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_841"), empty_list);
symInfo = listCons(stringValue("Function fn_841"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_848"), empty_list);
symInfo = listCons(stringValue("Function fn_848"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_851"), empty_list);
symInfo = listCons(stringValue("Function fn_851"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_858"), empty_list);
symInfo = listCons(stringValue("Function fn_858"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_861"), empty_list);
symInfo = listCons(stringValue("Function fn_861"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_864"), empty_list);
symInfo = listCons(stringValue("Function fn_864"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_871"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_871"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-found"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_883"), empty_list);
symInfo = listCons(stringValue("Function fn_883"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_891"), empty_list);
symInfo = listCons(stringValue("Function fn_891"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_894"), empty_list);
symInfo = listCons(stringValue("Function fn_894"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_897"), empty_list);
symInfo = listCons(stringValue("Function fn_897"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_900"), empty_list);
symInfo = listCons(stringValue("Function fn_900"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_903"), empty_list);
symInfo = listCons(stringValue("Function fn_903"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_906"), empty_list);
symInfo = listCons(stringValue("Function fn_906"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_909"), empty_list);
symInfo = listCons(stringValue("Function fn_909"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_912"), empty_list);
symInfo = listCons(stringValue("Function fn_912"), symInfo);
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
typeInfo = listCons(symbolValue("13"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(14), empty_list);
typeInfo = listCons(symbolValue("maybe-val"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(15), empty_list);
typeInfo = listCons(symbolValue("15"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(16), empty_list);
typeInfo = listCons(symbolValue("16"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(17), empty_list);
typeInfo = listCons(symbolValue("HashMap"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(18), empty_list);
typeInfo = listCons(symbolValue("18"), typeInfo);
types = listCons((Value *)typeInfo, types);
return((Value *)types);
}


Value *counts() {
List *cnts = empty_list;
cnts = listCons(numberValue(917), cnts);
return((Value *)cnts);
}

