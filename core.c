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
typedef struct {int64_t type; int32_t refs; int bitmap; Value *array[];} BitmapIndexedNode;
typedef struct {int64_t type; int32_t refs; Value *array[];} ArrayNode;
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
const int64_t BitmapIndexedType;
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
extern void free(void *);
extern void * malloc(unsigned long);
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
const int64_t BitmapIndexedType = 10;
List *empty_list = &(List){4,-1,0,0,0};

FILE *outStream;
Number trueVal = {2, -1, 1};
Value* true = (Value *)&trueVal;
Number falseVal = {2, -1, 0};
Value* false = (Value *)&falseVal;
long long malloc_count = 0;
long long free_count = 0;

int mask(int hash, int shift) {
  return (hash >> shift) & 0x1f;
}

int bitpos(int hash, int shift) {
  return 1 << mask(hash, shift);
}

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
  Value *val = malloc(sz);
  if (sz > sizeof(Value))
    val->refs = 1;
  return(val);
}

typedef struct DirectLL {int64_t type; struct DirectLL *next;} DirectLL;

DirectLL *freeSubStrings = (DirectLL *)0;
SubString *malloc_substring() {
  if (freeSubStrings == (DirectLL *)0) {
    malloc_count--;
    return((SubString *)my_malloc(sizeof(SubString)));
  } else {
    DirectLL *subStr = freeSubStrings;
    freeSubStrings = subStr->next;
    ((SubString *)subStr)->refs = 1;
    return((SubString *)subStr);
  }
}

int recycledReified = 0;
DirectLL *freeReified[20] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
ReifiedVal *malloc_reified(int implCount) {
  if (implCount > 19 || freeReified[implCount] == (DirectLL *)0) {
    malloc_count--;
    return((ReifiedVal *)my_malloc(sizeof(ReifiedVal) + sizeof(Function *) * implCount));
  } else {
    recycledReified++;    DirectLL *newReifiedVal = freeReified[implCount];
    freeReified[implCount] = newReifiedVal->next;
    ((ReifiedVal *)newReifiedVal)->refs = 1;
    return((ReifiedVal *)newReifiedVal);
  }
}

int recycledFunction = 0;
DirectLL *freeFunctions[10] = {0,0,0,0,0,0,0,0,0,0};
Function *malloc_function(int arityCount) {
  if (arityCount > 9 || freeFunctions[arityCount] == (DirectLL *)0) {
    malloc_count--;
    return((Function *)my_malloc(sizeof(Function) + sizeof(FnArity *) * arityCount));
  } else {
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
    malloc_count--;    for (int i = 99; i > 0; i--) {
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
    List *listStructs = (List *)my_malloc(sizeof(List) * 500);
    malloc_count--;
    for (int i = 499; i > 0; i--) {
      ((DirectLL *)&listStructs[i])->next = freeLists;
      freeLists = (DirectLL *)&listStructs[i];
    }
    return(listStructs);
  } else {
    DirectLL *newList = freeLists;
    freeLists = newList->next;
    ((List *)newList)->refs = 1;
    return((List *)newList);
  }
}

DirectLL *freeFnAritys = (DirectLL *)0;
FnArity *malloc_fnArity() {
  if (freeFnAritys == (DirectLL *)0) {
    malloc_count--;
    return((FnArity *)my_malloc(sizeof(FnArity)));
  } else {
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
  } else if (v->refs == -10) {
    fprintf(stderr, "freeing already freed struct\n");
    abort();
  } else if (v->refs > 0 || v->refs == -1) {
    return;
  } else if (v->type == 0) {
    fprintf(stderr, "freeing invalid type\n");
    abort();
  } else if (v->type == 1) {
    v->refs = -10;
    free_count++;
    free(v);
  } else if (v->type == 2) {
    v->refs = -10;
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
      free(v);
    }  } else if (v->type == 4) {
    Value *head = ((List *)v)->head;
    List *tail = ((List *)v)->tail;
    v->refs = -10;
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
    ((DirectLL *)v)->next = freeFnAritys;
    freeFnAritys = (DirectLL *)v;
  } else if (v->type == 9) {
    v->refs = -10;
  } else if (v->type == 10) {
    BitmapIndexedNode *node = (BitmapIndexedNode *)v;
    for (int i = 1; i < (2 * __builtin_popcount(node->bitmap)); i++) {
       if (node->array[i] != (Value *)0) {
          decRef(node->array[i]);
          my_free(node->array[i]);
       }
    }
    v->refs = -10;
    free_count++;
    free(v);
  } else if (v->type == 11) {
    ArrayNode *node = (ArrayNode *)v;
    for (int i = 1; i < 32; i++) {
       if (node->array[i] != (Value *)0) {
          decRef(node->array[i]);
          my_free(node->array[i]);
       }
    }
    v->refs = -10;
    free_count++;
    free(v);
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
      free(v);
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
Number _num_10 = {2, -1, 10};
Number _num_11 = {2, -1, 11};

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

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[18];} _str_9 = {1, -1, 17,"BitmapIndexedNode"};

// --------- type-name_impl --------------
Function fn_42;
Value *arityImpl_43(List *closures, Value *arg0) {
incRef((Value *)&_str_9);
return((Value *)&_str_9);
};


// --------- type-name_impl main body --------------
Function fn_42 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_43}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_10 = {1, -1, 9,"ArrayNode"};

// --------- type-name_impl --------------
Function fn_44;
Value *arityImpl_45(List *closures, Value *arg0) {
incRef((Value *)&_str_10);
return((Value *)&_str_10);
};


// --------- type-name_impl main body --------------
Function fn_44 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_45}}};

// forward declaration for 'print-err'
Value *var_46;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_11 = {1, -1, 4,"void"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_12 = {1, -1, 4,"char"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_13 = {1, -1, 6,"char *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[4];} _str_14 = {1, -1, 3,"int"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_15 = {1, -1, 7,"int64_t"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_16 = {1, -1, 52,"typedef struct {int64_t type; int32_t refs;} Value;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_17 = {1, -1, 7,"Value *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[70];} _str_18 = {1, -1, 69,"typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[83];} _str_19 = {1, -1, 82,"typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[99];} _str_20 = {1, -1, 98,"typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[102];} _str_21 = {1, -1, 101,"typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[106];} _str_22 = {1, -1, 105,"typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[108];} _str_23 = {1, -1, 107,"typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[58];} _str_24 = {1, -1, 57,"typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[88];} _str_25 = {1, -1, 87,"typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[89];} _str_26 = {1, -1, 88,"typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[65];} _str_27 = {1, -1, 64,"typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[93];} _str_28 = {1, -1, 92,"typedef struct {int64_t type; int32_t refs; int bitmap; Value *array[];} BitmapIndexedNode;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[73];} _str_29 = {1, -1, 72,"typedef struct {int64_t type; int32_t refs; Value *array[];} ArrayNode;\n"};
Value *var_67 = (Value *)&trueVal;;
Value *var_68 = (Value *)&falseVal;;

#include <stdint.h>
#include <memory.h>

typedef struct
{
    uint32_t        State[5];
    uint32_t        Count[2];
    uint8_t         Buffer[64];
} Sha1Context;

#define SHA1_HASH_SIZE           ( 64 / 8 )

typedef struct
{
    uint8_t      bytes [SHA1_HASH_SIZE];
} SHA1_HASH;

typedef union
{
    uint8_t     c [64];
    uint32_t    l [16];
} CHAR64LONG16;

#define rol(value, bits) (((value) << (bits)) | ((value) >> (32 - (bits))))
#define blk0(i) (block->l[i] = (rol(block->l[i],24)&0xFF00FF00) |(rol(block->l[i],8)&0x00FF00FF))
#define blk(i) (block->l[i&15] = rol(block->l[(i+13)&15]^block->l[(i+8)&15] ^block->l[(i+2)&15]^block->l[i&15],1))

#define R0(v,w,x,y,z,i)  z += ((w&(x^y))^y)     + blk0(i)+ 0x5A827999 + rol(v,5); w=rol(w,30);
#define R1(v,w,x,y,z,i)  z += ((w&(x^y))^y)     + blk(i) + 0x5A827999 + rol(v,5); w=rol(w,30);
#define R2(v,w,x,y,z,i)  z += (w^x^y)           + blk(i) + 0x6ED9EBA1 + rol(v,5); w=rol(w,30);
#define R3(v,w,x,y,z,i)  z += (((w|x)&y)|(w&x)) + blk(i) + 0x8F1BBCDC + rol(v,5); w=rol(w,30);
#define R4(v,w,x,y,z,i)  z += (w^x^y)           + blk(i) + 0xCA62C1D6 + rol(v,5); w=rol(w,30);


static void TransformFunction(uint32_t state[5], const uint8_t buffer[64]) {
    uint32_t            a;
    uint32_t            b;
    uint32_t            c;
    uint32_t            d;
    uint32_t            e;
    uint8_t             workspace[64];
    CHAR64LONG16*       block = (CHAR64LONG16*) workspace;

    memcpy( block, buffer, 64 );

    // Copy context->state[] to working vars
    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];

    // 4 rounds of 20 operations each. Loop unrolled.
    R0(a,b,c,d,e, 0); R0(e,a,b,c,d, 1); R0(d,e,a,b,c, 2); R0(c,d,e,a,b, 3);
    R0(b,c,d,e,a, 4); R0(a,b,c,d,e, 5); R0(e,a,b,c,d, 6); R0(d,e,a,b,c, 7);
    R0(c,d,e,a,b, 8); R0(b,c,d,e,a, 9); R0(a,b,c,d,e,10); R0(e,a,b,c,d,11);
    R0(d,e,a,b,c,12); R0(c,d,e,a,b,13); R0(b,c,d,e,a,14); R0(a,b,c,d,e,15);
    R1(e,a,b,c,d,16); R1(d,e,a,b,c,17); R1(c,d,e,a,b,18); R1(b,c,d,e,a,19);
    R2(a,b,c,d,e,20); R2(e,a,b,c,d,21); R2(d,e,a,b,c,22); R2(c,d,e,a,b,23);
    R2(b,c,d,e,a,24); R2(a,b,c,d,e,25); R2(e,a,b,c,d,26); R2(d,e,a,b,c,27);
    R2(c,d,e,a,b,28); R2(b,c,d,e,a,29); R2(a,b,c,d,e,30); R2(e,a,b,c,d,31);
    R2(d,e,a,b,c,32); R2(c,d,e,a,b,33); R2(b,c,d,e,a,34); R2(a,b,c,d,e,35);
    R2(e,a,b,c,d,36); R2(d,e,a,b,c,37); R2(c,d,e,a,b,38); R2(b,c,d,e,a,39);
    R3(a,b,c,d,e,40); R3(e,a,b,c,d,41); R3(d,e,a,b,c,42); R3(c,d,e,a,b,43);
    R3(b,c,d,e,a,44); R3(a,b,c,d,e,45); R3(e,a,b,c,d,46); R3(d,e,a,b,c,47);
    R3(c,d,e,a,b,48); R3(b,c,d,e,a,49); R3(a,b,c,d,e,50); R3(e,a,b,c,d,51);
    R3(d,e,a,b,c,52); R3(c,d,e,a,b,53); R3(b,c,d,e,a,54); R3(a,b,c,d,e,55);
    R3(e,a,b,c,d,56); R3(d,e,a,b,c,57); R3(c,d,e,a,b,58); R3(b,c,d,e,a,59);
    R4(a,b,c,d,e,60); R4(e,a,b,c,d,61); R4(d,e,a,b,c,62); R4(c,d,e,a,b,63);
    R4(b,c,d,e,a,64); R4(a,b,c,d,e,65); R4(e,a,b,c,d,66); R4(d,e,a,b,c,67);
    R4(c,d,e,a,b,68); R4(b,c,d,e,a,69); R4(a,b,c,d,e,70); R4(e,a,b,c,d,71);
    R4(d,e,a,b,c,72); R4(c,d,e,a,b,73); R4(b,c,d,e,a,74); R4(a,b,c,d,e,75);
    R4(e,a,b,c,d,76); R4(d,e,a,b,c,77); R4(c,d,e,a,b,78); R4(b,c,d,e,a,79);

    // Add the working vars back into context.state[]
    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
}

void Sha1Initialise (Sha1Context* Context) {
    // SHA1 initialization constants
    Context->State[0] = 0x67452301;
    Context->State[1] = 0xEFCDAB89;
    Context->State[2] = 0x98BADCFE;
    Context->State[3] = 0x10325476;
    Context->State[4] = 0xC3D2E1F0;
    Context->Count[0] = 0;
    Context->Count[1] = 0;
}

void Sha1Update (Sha1Context* Context, void* Buffer, uint32_t BufferSize) {
    uint32_t    i;
    uint32_t    j;

    j = (Context->Count[0] >> 3) & 63;
    if( (Context->Count[0] += BufferSize << 3) < (BufferSize << 3) )
    {
        Context->Count[1]++;
    }

    Context->Count[1] += (BufferSize >> 29);
    if( (j + BufferSize) > 63 )
    {
        i = 64 - j;
        memcpy( &Context->Buffer[j], Buffer, i );
        TransformFunction(Context->State, Context->Buffer);
        for( ; i + 63 < BufferSize; i += 64 )
        {
            TransformFunction(Context->State, (uint8_t*)Buffer + i);
        }
        j = 0;
    }
    else
    {
        i = 0;
    }

    memcpy( &Context->Buffer[j], &((uint8_t*)Buffer)[i], BufferSize - i );
}

void Sha1Finalise (Sha1Context* Context, SHA1_HASH* Digest) {
    uint32_t    i;
    uint8_t     finalcount[8];

    for( i=0; i<8; i++ )
    {
        finalcount[i] = (unsigned char)((Context->Count[(i >= 4 ? 0 : 1)]
         >> ((3-(i & 3)) * 8) ) & 255);  // Endian independent
    }
    Sha1Update( Context, (uint8_t*)"\x80", 1 );
    while( (Context->Count[0] & 504) != 448 )
    {
        Sha1Update( Context, (uint8_t*)"\0", 1 );
    }

    Sha1Update( Context, finalcount, 8 );  // Should cause a Sha1TransformFunction()
    for( i=0; i<SHA1_HASH_SIZE; i++ )
    {
        Digest->bytes[i] = (uint8_t)((Context->State[i>>2] >> ((3-(i & 3)) * 8) ) & 255);
    }
}

Value *valsEqual(List *, Value *, Value *);

int equal(Value *v1, Value *v2) {
  return (isTrue(valsEqual((List *)0, v1, v2)));
}

Value *assoc(Value *, Value *, Value *, Value *, Value *);

Value *sha1(Value *);

Value *hashSeq(Value* n, Value *s);

// --------- output-to-file --------------
Function fn_69;
Value *arityImpl_70(List *closures, Value *arg0) {
String *arg0Str = (String *)my_malloc(sizeof(String) + ((String *)arg0)->len + 5);
    arg0Str->type = StringType;
    if (arg0->type == StringType)
      snprintf(arg0Str->buffer, ((String *)arg0)->len + 1, "%s", ((String *)arg0)->buffer);
    else if (arg0->type == SubStringType)
      snprintf(arg0Str->buffer, ((String *)arg0)->len + 1, "%s", ((SubString *)arg0)->buffer);
    else {
      fprintf(stderr, "\ninvalid type for 'output-to-file'\n");
      abort();
    }

    outStream = fopen(arg0Str->buffer, "w");
    decRef((Value *)arg0Str);
    my_free((Value *)arg0Str);
    return((Value *)&trueVal);
};


// --------- output-to-file main body --------------
Function fn_69 = {3, -1, "output-to-file", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_70}}};


// --------- standard-output --------------
Function fn_72;
Value *arityImpl_73(List *closures) {
outStream = stdout;
    return((Value *)&trueVal);
};


// --------- standard-output main body --------------
Function fn_72 = {3, -1, "standard-output", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_73}}};


// --------- symkey-name --------------
Function fn_75;
Value *arityImpl_76(List *closures, Value *arg0) {
return(stringValue(((SubString *)arg0)->buffer));
};


// --------- symkey-name main body --------------
Function fn_75 = {3, -1, "symkey-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_76}}};


// --------- char-code --------------
Function fn_78;
Value *arityImpl_79(List *closures, Value *arg0) {
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
Function fn_78 = {3, -1, "char-code", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_79}}};


// --------- symbol --------------
Function fn_81;
Value *arityImpl_82(List *closures, Value *arg0) {
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
Function fn_81 = {3, -1, "symbol", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_82}}};


// --------- new-keyword --------------
Function fn_84;
Value *arityImpl_85(List *closures, Value *arg0) {
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
Function fn_84 = {3, -1, "new-keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_85}}};


// --------- abort --------------
Function fn_87;
Value *arityImpl_88(List *closures) {
abort();
    return(true);
};


// --------- abort main body --------------
Function fn_87 = {3, -1, "abort", 1, {&(FnArity){8, -1, 0, (List *)0, 0, arityImpl_88}}};


// --------- get-type --------------
Function fn_90;
Value *arityImpl_91(List *closures, Value *arg0) {
return(numberValue(arg0->type));};


// --------- get-type main body --------------
Function fn_90 = {3, -1, "get-type", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_91}}};


// --------- type= --------------
Function fn_93;
Value *arityImpl_94(List *closures, Value *arg0, Value *arg1) {
if (arg0->type == arg1->type)
                   return(true);
                else
                   return(false);
};


// --------- type= main body --------------
Function fn_93 = {3, -1, "type=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_94}}};


// --------- subs --------------
Function fn_96;
Value *arityImpl_97(List *closures, Value *arg0, Value *arg1) {
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

Value *arityImpl_98(List *closures, Value *arg0, Value *arg1, Value *arg2) {
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
Function fn_96 = {3, -1, "subs", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_97}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_98}}};


// --------- number-str --------------
Function fn_100;
Value *arityImpl_101(List *closures, Value *arg0) {
String *numStr = (String *)my_malloc(sizeof(String) + 10);
    snprintf(numStr->buffer, 9, "%lld", ((Number *)arg0)->numVal);
    numStr->type = StringType;
    numStr->len = strlen(numStr->buffer);
    return((Value *)numStr);
};


// --------- number-str main body --------------
Function fn_100 = {3, -1, "number-str", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_101}}};


// --------- number= --------------
Function fn_103;
Value *arityImpl_104(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      return(false);
   } else if (((Number *)arg0)->numVal != ((Number *)arg1)->numVal)
      return(false);
   else
      return(true);
};


// --------- number= main body --------------
Function fn_103 = {3, -1, "number=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_104}}};


// --------- number-less-than --------------
Function fn_106;
Value *arityImpl_107(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'number-less-than'\n");
      abort();
   } else if (((Number *)arg0)->numVal < ((Number *)arg1)->numVal)
      return(true);
   else
      return(false);
};


// --------- number-less-than main body --------------
Function fn_106 = {3, -1, "number-less-than", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_107}}};


// --------- add-numbers --------------
Function fn_109;
Value *arityImpl_110(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'add-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal + ((Number *)arg1)->numVal));
};


// --------- add-numbers main body --------------
Function fn_109 = {3, -1, "add-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_110}}};


// --------- subtract-numbers --------------
Function fn_112;
Value *arityImpl_113(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(outStream, "\ninvalid types for 'subtract-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal - ((Number *)arg1)->numVal));
};


// --------- subtract-numbers main body --------------
Function fn_112 = {3, -1, "subtract-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_113}}};


// --------- mult-numbers --------------
Function fn_115;
Value *arityImpl_116(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\n*** invalid types for 'mult-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal * ((Number *)arg1)->numVal));
};


// --------- mult-numbers main body --------------
Function fn_115 = {3, -1, "mult-numbers", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_116}}};


// --------- rem --------------
Function fn_118;
Value *arityImpl_119(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != NumberType ||
        arg1->type != NumberType) {
      fprintf(outStream, "\ninvalid types for 'rem'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal %
                         ((Number *)arg1)->numVal));
};


// --------- rem main body --------------
Function fn_118 = {3, -1, "rem", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_119}}};

Value *var_121 = (Value *)&(List){4,-1,0,0,0};;

// --------- cons --------------
Function fn_122;
Value *arityImpl_123(List *closures, Value *arg0) {
incRef(arg0);
return((Value *)listCons(arg0, empty_list));
};

Value *arityImpl_124(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
incRef(arg1);
return((Value *)listCons(arg0, (List *)arg1));
};


// --------- cons main body --------------
Function fn_122 = {3, -1, "cons", 2, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_123}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_124}}};


// --------- list-count --------------
Function fn_126;
Value *arityImpl_127(List *closures, Value *arg0) {
if (arg0->type != ListType)
      abort();
    else
      return(numberValue(((List *)arg0)->len));};


// --------- list-count main body --------------
Function fn_126 = {3, -1, "list-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_127}}};


// --------- car --------------
Function fn_129;
Value *arityImpl_130(List *closures, Value *arg0) {
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
Function fn_129 = {3, -1, "car", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_130}}};


// --------- cdr --------------
Function fn_132;
Value *arityImpl_133(List *closures, Value *arg0) {
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
Function fn_132 = {3, -1, "cdr", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_133}}};


// --------- fn-name --------------
Function fn_135;
Value *arityImpl_136(List *closures, Value *arg0) {
if (arg0->type != FunctionType) {
      fprintf(stderr, "\n*** invalid type for 'fn-name'\n");
      abort();
    } else
      return(stringValue(((Function *)arg0)->name));
};


// --------- fn-name main body --------------
Function fn_135 = {3, -1, "fn-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_136}}};


// --------- char --------------
Function fn_138;
Value *arityImpl_139(List *closures, Value *arg0) {
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
Function fn_138 = {3, -1, "char", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_139}}};


// --------- str-count --------------
Function fn_141;
Value *arityImpl_142(List *closures, Value *arg0) {
if (arg0->type != StringType && arg0->type != SubStringType ) {
      fprintf(outStream, "\ninvalid type for 'str-count'\n");
      abort();
    }
   return(numberValue(((String *)arg0)->len));
};


// --------- str-count main body --------------
Function fn_141 = {3, -1, "str-count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_142}}};


// --------- str= --------------
Function fn_144;
Value *arityImpl_145(List *closures, Value *arg0, Value *arg1) {
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
Function fn_144 = {3, -1, "str=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_145}}};


// --------- symkey= --------------
Function fn_147;
Value *arityImpl_148(List *closures, Value *arg0, Value *arg1) {
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
Function fn_147 = {3, -1, "symkey=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_148}}};


// --------- str-malloc --------------
Function fn_150;
Value *arityImpl_151(List *closures, Value *arg0) {
String *strVal = (String *)my_malloc(sizeof(String) + ((Number *)arg0)->numVal + 5);
    strVal->type = StringType;
    strVal->len = 0;
    strVal->buffer[0] = 0;
    return((Value *)strVal);
};


// --------- str-malloc main body --------------
Function fn_150 = {3, -1, "str-malloc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_151}}};


// --------- str-append --------------
Function fn_153;
Value *arityImpl_154(List *closures, Value *arg0, Value *arg1) {
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
Function fn_153 = {3, -1, "str-append", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_154}}};


// --------- pr-err* --------------
Function fn_156;
Value *arityImpl_157(List *closures, Value *arg0) {
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
Function fn_156 = {3, -1, "pr-err*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_157}}};


// --------- slurp --------------
Function fn_159;
Value *arityImpl_160(List *closures, Value *arg0) {
String *arg0Str = (String *)my_malloc(sizeof(String) + ((String *)arg0)->len + 5);
    arg0Str->type = StringType;
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
Function fn_159 = {3, -1, "slurp", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_160}}};


// --------- fn-apply --------------
Function fn_162;
Value *arityImpl_163(List *closures, Value *arg0, Value *arg1) {
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
Function fn_162 = {3, -1, "fn-apply", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_163}}};


// --------- escape-chars --------------
Function fn_165;
Value *arityImpl_166(List *closures, Value *arg0) {
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
Function fn_165 = {3, -1, "escape-chars", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_166}}};


// --------- pr* --------------
Function fn_168;
Value *arityImpl_169(List *closures, Value *arg0) {
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
Function fn_168 = {3, -1, "pr*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_169}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[16];} _str_30 = {1, -1, 15,":match*-one-arg"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[17];} _str_31 = {1, -1, 16,":match*-two-args"};
ProtoImpls *protoImpls_171;
Value *protoFnImpl_174(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_171);
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
FnArity protoFnArity_175 = {8, -1, 1, (List *)0, 0, protoFnImpl_174};
Function protoFn_172 = {3, -1, "bippity", 1, {&protoFnArity_175}};

ProtoImpls *protoImpls_176;
Value *arityImpl_179(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_169(empty_list, (Value *)&_str_30);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *protoFnImpl_180(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_176);
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
FnArity protoFnArity_181 = {8, -1, 1, (List *)0, 0, protoFnImpl_180};
Value *protoFnImpl_182(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_176);
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
FnArity protoFnArity_183 = {8, -1, 2, (List *)0, 0, protoFnImpl_182};
Function defaultFn_178 = {3, -1, "match*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_179}}};

Function protoFn_177 = {3, -1, "match*", 2, {&protoFnArity_181,
&protoFnArity_183}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_32 = {1, -1, 52,"*** call to 'instance?' with unknown type parameter."};
SubString _kw_0 = {5, -1, 2, 0, ":x"};
ProtoImpls *protoImpls_184;
Value *arityImpl_187(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_91(empty_list, arg0);
Value *rslt4 = arityImpl_104(empty_list, (Value *)&_num_2, rslt3);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
Value *rslt5 = arityImpl_91(empty_list, arg1);
Value *rslt6 = arityImpl_104(empty_list, arg0, rslt5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = arityImpl_169(empty_list, (Value *)&_str_32);
Value *rslt2 = arityImpl_88(empty_list);
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

Value *protoFnImpl_188(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_184);
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
FnArity protoFnArity_189 = {8, -1, 2, (List *)0, 0, protoFnImpl_188};
Function defaultFn_186 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_187}}};

Function protoFn_185 = {3, -1, "instance?", 1, {&protoFnArity_189}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_33 = {1, -1, 28,"'flat-map' not implemented: "};
ProtoImpls *protoImpls_190;
Value *arityImpl_193(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_3(empty_list, arg0);
Value *rslt4;
if((var_46)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_46, (Value *)&_str_33, rslt0);
} else {
FnArity *arity1 = findFnArity(var_46, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_46)->name);
  abort();
}
}
Value *rslt5 = arityImpl_88(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_194(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_190);
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
FnArity protoFnArity_195 = {8, -1, 2, (List *)0, 0, protoFnImpl_194};
Function defaultFn_192 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_193}}};

Function protoFn_191 = {3, -1, "flat-map", 1, {&protoFnArity_195}};

ProtoImpls *protoImpls_196;

// --------- anon --------------
Function fn_200;
Value *arityImpl_201(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- anon main body --------------
Function fn_200 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_201}}};

Value *arityImpl_199(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_194(empty_list, arg0, (Value *)&fn_200);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_202(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_196);
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
FnArity protoFnArity_203 = {8, -1, 1, (List *)0, 0, protoFnImpl_202};
Function defaultFn_198 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_199}}};

Function protoFn_197 = {3, -1, "flatten", 1, {&protoFnArity_203}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[30];} _str_34 = {1, -1, 29,"'duplicate' not implemented: "};
ProtoImpls *protoImpls_204;
Value *protoFnImpl_207(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_204);
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
FnArity protoFnArity_208 = {8, -1, 1, (List *)0, 0, protoFnImpl_207};
Function protoFn_205 = {3, -1, "extract", 1, {&protoFnArity_208}};

ProtoImpls *protoImpls_209;
Value *protoFnImpl_212(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_209);
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
FnArity protoFnArity_213 = {8, -1, 2, (List *)0, 0, protoFnImpl_212};
Function protoFn_210 = {3, -1, "extend", 1, {&protoFnArity_213}};

ProtoImpls *protoImpls_214;
Value *arityImpl_217(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_3(empty_list, arg0);
Value *rslt4;
if((var_46)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_46, (Value *)&_str_34, rslt0);
} else {
FnArity *arity1 = findFnArity(var_46, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_46)->name);
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

Value *protoFnImpl_218(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_214);
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
FnArity protoFnArity_219 = {8, -1, 1, (List *)0, 0, protoFnImpl_218};
Function defaultFn_216 = {3, -1, "duplicate", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_217}}};

Function protoFn_215 = {3, -1, "duplicate", 1, {&protoFnArity_219}};

// forward declaration for 'comprehend'
Value *var_220;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_35 = {1, -1, 26,"*** 'wrap' not implemented"};
Number _num_12 = {2, -1, 0};
ProtoImpls *protoImpls_221;
Value *arityImpl_224(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_46)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_46, (Value *)&_str_35);
} else {
FnArity *arity0 = findFnArity(var_46, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_35);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef((Value *)&_str_35);
varArgs1 = (List *)listCons((Value *)&_str_35, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_46)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *protoFnImpl_225(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_221);
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
FnArity protoFnArity_226 = {8, -1, 2, (List *)0, 0, protoFnImpl_225};
Function defaultFn_223 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_224}}};

Function protoFn_222 = {3, -1, "wrap", 1, {&protoFnArity_226}};

ProtoImpls *protoImpls_227;

// --------- anon --------------
Function fn_231;
Value *arityImpl_232(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt4;
if((var_220)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_220, arg0, val0);
} else {
FnArity *arity1 = findFnArity(var_220, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_220)->name);
  abort();
}
}
incRef(rslt4);
decRef(rslt4);
my_free(rslt4);
return(rslt4);
};


// --------- anon --------------
Function fn_233;
Value *arityImpl_234(List *closures, Value *arg0) {
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
Value *rslt5 = protoFnImpl_225(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_230(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_127(empty_list, arg1);
Value *rslt4 = arityImpl_104(empty_list, (Value *)&_num_12, rslt3);
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
arity_5->fn = arityImpl_234;
incRef((Value *)arg0);
arity_5->closures = listCons((Value *)arg0, (List *)arity_5->closures);
Function *fn_233 = malloc_function(1);
fn_233->type = 3;
fn_233->name = "anon";
fn_233->arityCount = 1;
fn_233->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_194(empty_list, arg0, (Value *)fn_233);
incRef(rslt6);
cond0 = rslt6;
decRef((Value *)fn_233);
my_free((Value *)fn_233);
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
arity_1->fn = arityImpl_232;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_231 = malloc_function(1);
fn_231->type = 3;
fn_231->name = "anon";
fn_231->arityCount = 1;
fn_231->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_194(empty_list, arg0, (Value *)fn_231);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_231);
my_free((Value *)fn_231);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

Value *protoFnImpl_235(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_227);
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
FnArity protoFnArity_236 = {8, -1, 2, (List *)0, 0, protoFnImpl_235};
Function defaultFn_229 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_230}}};

Function protoFn_228 = {3, -1, "apply*", 1, {&protoFnArity_236}};


// --------- apply --------------
Function fn_237;
Value *arityImpl_238(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = protoFnImpl_235(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- apply main body --------------
Function fn_237 = {3, -1, "apply", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_238}}};


// --------- apply-to --------------
Function fn_240;
Value *arityImpl_241(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt4 = arityImpl_127(empty_list, arg1);
Value *rslt5 = arityImpl_104(empty_list, (Value *)&_num_12, rslt4);
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
Value *rslt1 = arityImpl_130(empty_list, arg1);
Value *rslt2 = protoFnImpl_225(empty_list, rslt1, arg0);
Value *rslt3 = protoFnImpl_235(empty_list, rslt2, arg1);
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
Function fn_240 = {3, -1, "apply-to", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_241}}};


// --------- list --------------
Function fn_243;
Value *arityImpl_244(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_243 = {3, -1, "list", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_244}}};

ProtoImpls *protoImpls_246;

// --------- anon --------------
Function fn_250;
Value *arityImpl_251(List *closures, Value *arg0) {
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
Value *rslt6 = protoFnImpl_225(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_249(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_251;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_250 = malloc_function(1);
fn_250->type = 3;
fn_250->name = "anon";
fn_250->arityCount = 1;
fn_250->arities[0] = arity_0;
Value *rslt1 = protoFnImpl_194(empty_list, arg0, (Value *)fn_250);
incRef(rslt1);
decRef((Value *)fn_250);
my_free((Value *)fn_250);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoFnImpl_252(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_246);
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
FnArity protoFnArity_253 = {8, -1, 2, (List *)0, 0, protoFnImpl_252};
Function defaultFn_248 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_249}}};

Function protoFn_247 = {3, -1, "map", 1, {&protoFnArity_253}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_36 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_254;
Value *arityImpl_257(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt4;
if((var_46)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_46, (Value *)&_str_36, rslt0);
} else {
FnArity *arity1 = findFnArity(var_46, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_36, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_36);
varArgs2 = (List *)listCons((Value *)&_str_36, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_46)->name);
  abort();
}
}
Value *rslt5 = arityImpl_88(empty_list);
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
FnArity protoFnArity_259 = {8, -1, 1, (List *)0, 0, protoFnImpl_258};
Function defaultFn_256 = {3, -1, "name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_257}}};

Function protoFn_255 = {3, -1, "name", 1, {&protoFnArity_259}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_37 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_260;
Value *arityImpl_263(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt4;
if((var_46)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_46, (Value *)&_str_37, rslt0);
} else {
FnArity *arity1 = findFnArity(var_46, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_37, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_37);
varArgs2 = (List *)listCons((Value *)&_str_37, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_46)->name);
  abort();
}
}
Value *rslt5 = arityImpl_88(empty_list);
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
FnArity protoFnArity_265 = {8, -1, 1, (List *)0, 0, protoFnImpl_264};
Function defaultFn_262 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_263}}};

Function protoFn_261 = {3, -1, "string-list", 1, {&protoFnArity_265}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_38 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_266;
Value *arityImpl_269(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt4;
if((var_46)->type != 3) {
rslt4 = protoFnImpl_12(empty_list, var_46, (Value *)&_str_38, rslt0);
} else {
FnArity *arity1 = findFnArity(var_46, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_38, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_38);
varArgs2 = (List *)listCons((Value *)&_str_38, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_46)->name);
  abort();
}
}
Value *rslt5 = arityImpl_88(empty_list);
incRef(rslt5);
decRef(rslt0);
my_free(rslt0);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_270(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_266);
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
FnArity protoFnArity_271 = {8, -1, 1, (List *)0, 0, protoFnImpl_270};
Function defaultFn_268 = {3, -1, "serialize", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_269}}};

Function protoFn_267 = {3, -1, "serialize", 1, {&protoFnArity_271}};


// --------- list-empty? --------------
Function fn_272;
Value *arityImpl_273(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_127(empty_list, arg0);
Value *rslt1 = arityImpl_104(empty_list, (Value *)&_num_12, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- list-empty? main body --------------
Function fn_272 = {3, -1, "list-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_273}}};


// --------- interpose --------------
Function fn_275;

// --------- anon --------------
Function fn_277;
Value *arityImpl_278(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)val0);
varArgs1 = (List *)listCons((Value *)val0, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
incRef(rslt2);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *arityImpl_276(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = arityImpl_273(empty_list, arg0);
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
Value *rslt1 = arityImpl_130(empty_list, arg0);
Value *rslt2 = arityImpl_133(empty_list, arg0);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_278;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_277 = malloc_function(1);
fn_277->type = 3;
fn_277->name = "anon";
fn_277->arityCount = 1;
fn_277->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_194(empty_list, rslt2, (Value *)fn_277);
Value *rslt5 = arityImpl_124(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_277);
my_free((Value *)fn_277);
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
Function fn_275 = {3, -1, "interpose", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_276}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_39 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_40 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_280;
Value *arityImpl_281(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = protoFnImpl_194(empty_list, arg0, (Value *)&protoFn_267);
Value *rslt1 = arityImpl_276(empty_list, rslt0, (Value *)&_str_39);
Value *rslt2 = protoFnImpl_252(empty_list, rslt1, (Value *)&fn_168);
Value *rslt3 = arityImpl_169(empty_list, (Value *)&_str_40);
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
Function fn_280 = {3, -1, "prn", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_281}}};


// --------- print --------------
Function fn_283;
Value *arityImpl_284(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_276(empty_list, arg0, (Value *)&_str_39);
Value *rslt1 = protoFnImpl_194(empty_list, rslt0, (Value *)&protoFn_261);
Value *rslt2 = protoFnImpl_252(empty_list, rslt1, (Value *)&fn_168);
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
Function fn_283 = {3, -1, "print", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_284}}};


// --------- println --------------
Function fn_286;
Value *arityImpl_287(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_276(empty_list, arg0, (Value *)&_str_39);
Value *rslt1 = protoFnImpl_194(empty_list, rslt0, (Value *)&protoFn_261);
Value *rslt2 = protoFnImpl_252(empty_list, rslt1, (Value *)&fn_168);
Value *rslt3 = arityImpl_169(empty_list, (Value *)&_str_40);
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
Function fn_286 = {3, -1, "println", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_287}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_41 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_289;
Value *arityImpl_290(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_157(empty_list, (Value *)&_str_41);
Value *rslt1 = arityImpl_276(empty_list, arg0, (Value *)&_str_39);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, (Value *)&protoFn_261);
Value *rslt3 = protoFnImpl_252(empty_list, rslt2, (Value *)&fn_156);
Value *rslt4 = arityImpl_157(empty_list, (Value *)&_str_40);
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
Function fn_289 = {3, -1, "print-err", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_290}}};

Value *var_46 = (Value *)&fn_289;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_42 = {1, -1, 21,"'=*' not implemented:"};
ProtoImpls *protoImpls_291;
Value *arityImpl_294(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_42);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_42, varArgs0);
Value *rslt1 = arityImpl_290(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_88(empty_list);
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
FnArity protoFnArity_296 = {8, -1, 2, (List *)0, 0, protoFnImpl_295};
Function defaultFn_293 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_294}}};

Function protoFn_292 = {3, -1, "=*", 1, {&protoFnArity_296}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_43 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_297;
Value *arityImpl_300(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_43);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_43, varArgs0);
Value *rslt1 = arityImpl_290(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_88(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_301(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_297);
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
FnArity protoFnArity_302 = {8, -1, 2, (List *)0, 0, protoFnImpl_301};
Function defaultFn_299 = {3, -1, "<*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_300}}};

Function protoFn_298 = {3, -1, "<*", 1, {&protoFnArity_302}};

ProtoImpls *protoImpls_303;
Value *protoFnImpl_306(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_303);
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
FnArity protoFnArity_307 = {8, -1, 1, (List *)0, 0, protoFnImpl_306};
Function protoFn_304 = {3, -1, "empty?", 1, {&protoFnArity_307}};

ProtoImpls *protoImpls_308;
Value *protoFnImpl_311(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_308);
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
FnArity protoFnArity_312 = {8, -1, 1, (List *)0, 0, protoFnImpl_311};
Function protoFn_309 = {3, -1, "empty", 1, {&protoFnArity_312}};

ProtoImpls *protoImpls_313;
Value *protoFnImpl_316(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_313);
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
FnArity protoFnArity_317 = {8, -1, 2, (List *)0, 0, protoFnImpl_316};
Function protoFn_314 = {3, -1, "destruct", 1, {&protoFnArity_317}};

ProtoImpls *protoImpls_318;
Value *protoFnImpl_321(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_318);
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
FnArity protoFnArity_322 = {8, -1, 1, (List *)0, 0, protoFnImpl_321};
Function protoFn_319 = {3, -1, "count", 1, {&protoFnArity_322}};

ProtoImpls *protoImpls_323;
Value *protoFnImpl_326(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_323);
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
FnArity protoFnArity_327 = {8, -1, 2, (List *)0, 0, protoFnImpl_326};
Function protoFn_324 = {3, -1, "conj", 1, {&protoFnArity_327}};

ProtoImpls *protoImpls_328;
Value *protoFnImpl_331(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_328);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'reduce' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 3);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'reduce'\n");
    abort();
}
  FnType3 *_fn = (FnType3 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2));
}
FnArity protoFnArity_332 = {8, -1, 3, (List *)0, 0, protoFnImpl_331};
Function protoFn_329 = {3, -1, "reduce", 1, {&protoFnArity_332}};


// --------- not-empty? --------------
Function fn_333;
Value *arityImpl_334(List *closures, Value *arg0) {
Value *cond0;
Value *rslt1 = protoFnImpl_306(empty_list, arg0);
decRef(rslt1);
my_free(rslt1);

if (isTrue(rslt1)) {
decRef(rslt1);
my_free(rslt1);
incRef(var_68);
cond0 = var_68;
} else {
decRef(rslt1);
my_free(rslt1);
incRef(var_67);
cond0 = var_67;
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- not-empty? main body --------------
Function fn_333 = {3, -1, "not-empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_334}}};

ProtoImpls *protoImpls_336;
Value *arityImpl_339(List *closures, Value *arg0) {
incRef(var_68);
return(var_68);
};

Value *protoFnImpl_340(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_336);
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
FnArity protoFnArity_341 = {8, -1, 1, (List *)0, 0, protoFnImpl_340};
Function defaultFn_338 = {3, -1, "seq?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_339}}};

Function protoFn_337 = {3, -1, "seq?", 1, {&protoFnArity_341}};

ProtoImpls *protoImpls_342;
Value *protoFnImpl_345(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_342);
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
FnArity protoFnArity_346 = {8, -1, 1, (List *)0, 0, protoFnImpl_345};
Function protoFn_343 = {3, -1, "seq", 1, {&protoFnArity_346}};

ProtoImpls *protoImpls_347;
Value *protoFnImpl_350(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_347);
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
FnArity protoFnArity_351 = {8, -1, 1, (List *)0, 0, protoFnImpl_350};
Function protoFn_348 = {3, -1, "first", 1, {&protoFnArity_351}};

ProtoImpls *protoImpls_352;
Value *protoFnImpl_355(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_352);
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
FnArity protoFnArity_356 = {8, -1, 1, (List *)0, 0, protoFnImpl_355};
Function protoFn_353 = {3, -1, "rest", 1, {&protoFnArity_356}};


// --------- second --------------
Function fn_357;
Value *arityImpl_358(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_355(empty_list, arg0);
Value *rslt1 = protoFnImpl_350(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- second main body --------------
Function fn_357 = {3, -1, "second", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_358}}};

ProtoImpls *protoImpls_360;
Value *protoFnImpl_363(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_360);
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
FnArity protoFnArity_364 = {8, -1, 2, (List *)0, 0, protoFnImpl_363};
Function protoFn_361 = {3, -1, "traverse", 1, {&protoFnArity_364}};

ProtoImpls *protoImpls_365;
Value *protoFnImpl_368(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_365);
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
FnArity protoFnArity_369 = {8, -1, 2, (List *)0, 0, protoFnImpl_368};
Function protoFn_366 = {3, -1, "crush", 1, {&protoFnArity_369}};

ProtoImpls *protoImpls_370;
Value *protoFnImpl_373(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_370);
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
FnArity protoFnArity_374 = {8, -1, 1, (List *)0, 0, protoFnImpl_373};
Function protoFn_371 = {3, -1, "zero", 1, {&protoFnArity_374}};

ProtoImpls *protoImpls_375;
Value *protoFnImpl_378(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_375);
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
FnArity protoFnArity_379 = {8, -1, 2, (List *)0, 0, protoFnImpl_378};
Function protoFn_376 = {3, -1, "comp*", 1, {&protoFnArity_379}};


// --------- comp --------------
Function fn_380;
Value *arityImpl_381(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_378(empty_list, arg0, arg1);
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
Function fn_380 = {3, -1, "comp", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_381}}};

ProtoImpls *protoImpls_383;
Value *protoFnImpl_386(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_383);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'hash-seq' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'hash-seq'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_387 = {8, -1, 2, (List *)0, 0, protoFnImpl_386};
Function protoFn_384 = {3, -1, "hash-seq", 1, {&protoFnArity_387}};

ProtoImpls *protoImpls_388;
Value *protoFnImpl_391(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_388);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'assoc*' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 5);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'assoc*'\n");
    abort();
}
  FnType5 *_fn = (FnType5 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3, arg4));
}
FnArity protoFnArity_392 = {8, -1, 5, (List *)0, 0, protoFnImpl_391};
Function protoFn_389 = {3, -1, "assoc*", 1, {&protoFnArity_392}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[24];} _str_44 = {1, -1, 23,"'get' not implemented: "};
SubString _kw_1 = {5, -1, 2, 0, ":m"};
SubString _kw_2 = {5, -1, 2, 0, ":k"};
ProtoImpls *protoImpls_393;
Value *protoFnImpl_396(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_393);
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
FnArity protoFnArity_397 = {8, -1, 3, (List *)0, 0, protoFnImpl_396};
Function protoFn_394 = {3, -1, "assoc", 1, {&protoFnArity_397}};

ProtoImpls *protoImpls_398;
Value *arityImpl_401(List *closures, Value *arg0, Value *arg1, Value *arg2) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)(Value *)&_kw_2);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_2, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_kw_1);
varArgs0 = (List *)listCons((Value *)(Value *)&_kw_1, varArgs0);
incRef((Value *)(Value *)&_str_44);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_44, varArgs0);
Value *rslt1 = arityImpl_290(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_88(empty_list);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};

Value *protoFnImpl_402(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_398);
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
FnArity protoFnArity_403 = {8, -1, 3, (List *)0, 0, protoFnImpl_402};
Function defaultFn_400 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_401}}};

Function protoFn_399 = {3, -1, "get", 1, {&protoFnArity_403}};

ProtoImpls *protoImpls_404;
Value *protoFnImpl_407(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_404);
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
FnArity protoFnArity_408 = {8, -1, 1, (List *)0, 0, protoFnImpl_407};
Function protoFn_405 = {3, -1, "keys", 1, {&protoFnArity_408}};

ProtoImpls *protoImpls_409;
Value *protoFnImpl_412(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_409);
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
FnArity protoFnArity_413 = {8, -1, 1, (List *)0, 0, protoFnImpl_412};
Function protoFn_410 = {3, -1, "vals", 1, {&protoFnArity_413}};

ProtoImpls *protoImpls_414;
Value *protoFnImpl_417(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_414);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'sha1' %s\n", extractStr(protoFnImpl_3(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'sha1'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_418 = {8, -1, 1, (List *)0, 0, protoFnImpl_417};
Function protoFn_415 = {3, -1, "sha1", 1, {&protoFnArity_418}};


// --------- not --------------
Function fn_419;
Value *arityImpl_420(List *closures, Value *arg0) {
Value *cond0;

if (isTrue(arg0)) {
decRef(arg0);
my_free(arg0);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
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
Function fn_419 = {3, -1, "not", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_420}}};


// --------- and --------------
Function fn_422;
Value *arityImpl_423(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt1 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt2 = protoFnImpl_350(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
Value *rslt3 = protoFnImpl_355(empty_list, arg0);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_422);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_422, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
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
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
}
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- and main body --------------
Function fn_422 = {3, -1, "and", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_423}}};


// --------- or --------------
Function fn_425;
Value *arityImpl_426(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt4 = protoFnImpl_306(empty_list, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt5 = protoFnImpl_350(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_355(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)(Value *)&fn_425);
varArgs2 = (List *)listCons((Value *)(Value *)&fn_425, varArgs2);
Value *rslt3 = arityImpl_238(empty_list, (Value *)varArgs2);
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
Function fn_425 = {3, -1, "or", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_426}}};


// --------- = --------------
Function fn_428;
Value *arityImpl_429(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_295(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_430(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_350(empty_list, arg1);
Value *rslt5 = protoFnImpl_295(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_420(empty_list, rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_321(empty_list, arg1);
Value *rslt8 = arityImpl_104(empty_list, (Value *)&_num_1, rslt7);
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
incRef((Value *)(Value *)&fn_428);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_428, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
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
Function fn_428 = {3, -1, "=", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_429}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_430}}};


// --------- < --------------
Function fn_432;
Value *arityImpl_433(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_301(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

Value *arityImpl_434(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt4 = protoFnImpl_350(empty_list, arg1);
Value *rslt5 = protoFnImpl_301(empty_list, arg0, rslt4);
Value *rslt6 = arityImpl_420(empty_list, rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_321(empty_list, arg1);
Value *rslt8 = arityImpl_104(empty_list, (Value *)&_num_1, rslt7);
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
incRef((Value *)(Value *)&fn_432);
varArgs1 = (List *)listCons((Value *)(Value *)&fn_432, varArgs1);
Value *rslt2 = arityImpl_238(empty_list, (Value *)varArgs1);
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
Function fn_432 = {3, -1, "<", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_433}, &(FnArity){8, -1, 2, (List *)0, 1, arityImpl_434}}};


// --------- list** --------------
Function fn_436;
Value *arityImpl_437(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_355(empty_list, arg1);
Value *rslt3 = arityImpl_437(closures, rslt1, rslt2);
Value *rslt4 = arityImpl_124(empty_list, arg0, rslt3);
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
Function fn_436 = {3, -1, "list**", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_437}}};


// --------- list* --------------
Function fn_439;
Value *arityImpl_440(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *)argsList;
Value *rslt0 = arityImpl_437(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};

// --------- list* main body --------------
Function fn_439 = {3, -1, "list*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_440}}};


// --------- filter --------------
Function fn_442;
Value *arityImpl_443(List *closures, Value *arg0, Value *arg1) {
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
Function fn_442 = {3, -1, "filter", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_443}}};


// --------- remove --------------
Function fn_445;

// --------- anon --------------
Function fn_447;
Value *arityImpl_448(List *closures, Value *arg0) {
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
Value *rslt5 = arityImpl_420(empty_list, rslt4);
incRef(rslt5);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_446(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_448;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_447 = malloc_function(1);
fn_447->type = 3;
fn_447->name = "anon";
fn_447->arityCount = 1;
fn_447->arities[0] = arity_0;
Value *rslt1 = arityImpl_443(empty_list, arg0, (Value *)fn_447);
incRef(rslt1);
decRef((Value *)fn_447);
my_free((Value *)fn_447);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- remove main body --------------
Function fn_445 = {3, -1, "remove", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_446}}};


// --------- reverse --------------
Function fn_450;
Value *arityImpl_451(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_311(empty_list, arg0);
Value *rslt1 = protoFnImpl_331(empty_list, arg0, rslt0, (Value *)&protoFn_324);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- reverse main body --------------
Function fn_450 = {3, -1, "reverse", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_451}}};


// --------- identity --------------
Function fn_453;
Value *arityImpl_454(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_453 = {3, -1, "identity", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_454}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_45 = {1, -1, 5,"<Fn: "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_46 = {1, -1, 1,">"};

// --------- string-list_impl --------------
Function fn_456;
Value *arityImpl_457(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_136(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_46, varArgs1);
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
incRef((Value *)(Value *)&_str_45);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_45, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
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
Function fn_456 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_457}}};


// --------- zero_impl --------------
Function fn_458;
Value *arityImpl_459(List *closures, Value *arg0) {
incRef((Value *)&fn_453);
return((Value *)&fn_453);
};


// --------- zero_impl main body --------------
Function fn_458 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_459}}};


// --------- comp*_impl --------------
Function fn_460;

// --------- anon --------------
Function fn_462;

// --------- anon --------------
Function fn_464;
Value *arityImpl_465(List *closures, Value *arg0, Value *arg1) {
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
Function fn_464 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_465}}};

Value *arityImpl_463(List *closures, Value *varArgs) {
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
Value *rslt3 = arityImpl_238(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
Value *rslt5 = protoFnImpl_331(empty_list, val0, rslt3, (Value *)&fn_464);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_461(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_463;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_462 = malloc_function(1);
fn_462->type = 3;
fn_462->name = "anon";
fn_462->arityCount = 1;
fn_462->arities[0] = arity_0;
incRef((Value *)fn_462);
decRef((Value *)fn_462);
my_free((Value *)fn_462);
return((Value *)fn_462);
};


// --------- comp*_impl main body --------------
Function fn_460 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_461}}};


// --------- apply*_impl --------------
Function fn_466;
Value *arityImpl_467(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_355(empty_list, arg1);
Value *rslt3 = arityImpl_437(empty_list, rslt1, rslt2);
Value *rslt4 = arityImpl_163(empty_list, arg0, rslt3);
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
Function fn_466 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_467}}};


// --------- =*_impl --------------
Function fn_468;
Value *arityImpl_469(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_104(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_468 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_469}}};


// --------- <*_impl --------------
Function fn_470;
Value *arityImpl_471(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_107(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- <*_impl main body --------------
Function fn_470 = {3, -1, "<*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_471}}};


// --------- string-list_impl --------------
Function fn_472;
Value *arityImpl_473(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_101(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
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
Function fn_472 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_473}}};


// --------- any? --------------
Function fn_474;
Value *arityImpl_475(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg1);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_350(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_355(empty_list, arg1);
Value *rslt2 = arityImpl_475(closures, arg0, rslt1);
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
Function fn_474 = {3, -1, "any?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_475}}};

ProtoImpls *protoImpls_477;
Value *protoFnImpl_480(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_477);
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
FnArity protoFnArity_481 = {8, -1, 1, (List *)0, 0, protoFnImpl_480};
Function protoFn_478 = {3, -1, ".v", 1, {&protoFnArity_481}};

// forward declaration for 'ZipList'
Value *var_482;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_47 = {1, -1, 7,"ZipList"};
Number _num_13 = {2, -1, 13};
SubString _kw_3 = {5, -1, 4, 0, ":nil"};

// --------- instance?_impl --------------
Function fn_483;
Value *arityImpl_484(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_91(empty_list, arg1);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_13, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_483 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_484}}};

Value *protoImpl_485(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_486 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_485}}};


// --------- invoke_impl --------------
Function fn_487;

// --------- apply*_impl --------------
Function fn_489;

// --------- anon --------------
Function fn_491;
Value *arityImpl_492(List *closures, Value *arg0) {
Value *cond0;
Value *rslt2 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg0);
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
Function fn_491 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_492}}};

Value *arityImpl_490(List *closures, Value *arg0, Value *arg1) {
Value *val4 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt9 = arityImpl_475(empty_list, (Value *)&protoFn_304, arg1);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt2 = protoFnImpl_252(empty_list, arg1, (Value *)&fn_491);
Value *rslt3 = protoFnImpl_252(empty_list, arg1, (Value *)&protoFn_353);
List *varArgs5 = empty_list;
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
incRef((Value *)val4);
varArgs5 = (List *)listCons((Value *)val4, varArgs5);
Value *rslt6 = arityImpl_238(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_235(empty_list, arg0, rslt3);
Value *rslt8 = arityImpl_124(empty_list, rslt6, rslt7);
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

Value *protoImpl_493(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_494 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_493}}};


// --------- type-name_impl --------------
Function fn_495;
Value *arityImpl_496(List *closures, Value *arg0) {
incRef((Value *)&_str_47);
return((Value *)&_str_47);
};


// --------- type-name_impl main body --------------
Function fn_495 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_496}}};

Value *protoImpl_497(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_498 = {3, -1, "type-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_497}}};


// --------- .v_impl --------------
Function fn_499;
Value *arityImpl_500(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_501(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_502 = {3, -1, ".v", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_501}}};

Value *arityImpl_488(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_490;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_489 = malloc_function(1);
fn_489->type = 3;
fn_489->name = "apply*_impl";
fn_489->arityCount = 1;
fn_489->arities[0] = arity_0;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = 8;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_500;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_499 = malloc_function(1);
fn_499->type = 3;
fn_499->name = ".v_impl";
fn_499->arityCount = 1;
fn_499->arities[0] = arity_2;
Value *reified_3 = (Value *)malloc_reified(3);
((ReifiedVal *)reified_3)->type = 13;
((ReifiedVal *)reified_3)->implCount = 3;
((ReifiedVal *)reified_3)->impls[0] = (Value *)fn_489;
incRef((Value *)fn_489);
((ReifiedVal *)reified_3)->impls[1] = (Value *)&fn_495;
incRef((Value *)&fn_495);
((ReifiedVal *)reified_3)->impls[2] = (Value *)fn_499;
incRef((Value *)fn_499);
incRef(reified_3);
decRef((Value *)fn_489);
my_free((Value *)fn_489);
decRef((Value *)fn_499);
my_free((Value *)fn_499);
decRef(reified_3);
my_free(reified_3);
return(reified_3);
};


// --------- invoke_impl main body --------------
Function fn_487 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_488}}};

Value *protoImpl_503(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_504 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_503}}};

ReifiedVal reified_505 = {12, -1, 2, {(Value *)&fn_483, (Value *)&fn_487}};
Value *var_482 = (Value *)&reified_505;

// --------- partial --------------
Function fn_506;

// --------- anon --------------
Function fn_508;
Value *arityImpl_509(List *closures, Value *varArgs) {
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
Value *rslt3 = arityImpl_381(empty_list, (Value *)varArgs2);
decRef((Value *)varArgs2);
my_free((Value *)varArgs2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val0);
varArgs4 = (List *)listCons((Value *)val0, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
incRef(rslt5);
decRef(rslt3);
my_free(rslt3);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};
Value *arityImpl_507(List *closures, Value *varArgs) {
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
arity_0->fn = arityImpl_509;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_508 = malloc_function(1);
fn_508->type = 3;
fn_508->name = "anon";
fn_508->arityCount = 1;
fn_508->arities[0] = arity_0;
incRef((Value *)fn_508);
decRef((Value *)fn_508);
my_free((Value *)fn_508);
return((Value *)fn_508);
};

// --------- partial main body --------------
Function fn_506 = {3, -1, "partial", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_507}}};


// --------- comprehend --------------
Function fn_511;

// --------- anon --------------
Function fn_513;
Value *arityImpl_514(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_124(empty_list, arg1, arg0);
Value *rslt3 = arityImpl_451(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)val1);
varArgs4 = (List *)listCons((Value *)val1, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = protoFnImpl_225(empty_list, val0, rslt5);
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
Function fn_515;

// --------- anon --------------
Function fn_517;
Value *arityImpl_518(List *closures, Value *arg0, Value *arg1) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt2 = arityImpl_124(empty_list, arg1, arg0);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)val1);
varArgs3 = (List *)listCons((Value *)val1, varArgs3);
Value *rslt4 = arityImpl_507(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_194(empty_list, val0, rslt4);
incRef(rslt5);
decRef(rslt2);
my_free(rslt2);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
return(rslt5);
};

Value *arityImpl_516(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_518;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_517 = malloc_function(1);
fn_517->type = 3;
fn_517->name = "anon";
fn_517->arityCount = 1;
fn_517->arities[0] = arity_0;
incRef((Value *)fn_517);
decRef((Value *)fn_517);
my_free((Value *)fn_517);
return((Value *)fn_517);
};


// --------- anon main body --------------
Function fn_515 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_516}}};


// --------- anon --------------
Function fn_519;
Value *arityImpl_520(List *closures, Value *arg0) {
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
Value *rslt6 = protoFnImpl_225(empty_list, val0, rslt5);
incRef(rslt6);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_512(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt16 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_355(empty_list, arg1);
Value *rslt3 = arityImpl_451(empty_list, rslt2);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_514;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
incRef((Value *)rslt1);
arity_4->closures = listCons((Value *)rslt1, (List *)arity_4->closures);
Function *fn_513 = malloc_function(1);
fn_513->type = 3;
fn_513->name = "anon";
fn_513->arityCount = 1;
fn_513->arities[0] = arity_4;
Value *rslt6 = protoFnImpl_331(empty_list, rslt3, (Value *)fn_513, (Value *)&fn_515);
Value *cond7;
Value *rslt11 = protoFnImpl_321(empty_list, arg1);
Value *rslt12 = arityImpl_104(empty_list, (Value *)&_num_1, rslt11);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
Value *rslt13 = protoFnImpl_350(empty_list, arg1);
FnArity *arity_14 = malloc_fnArity();
arity_14->type = 8;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_520;
incRef((Value *)arg0);
arity_14->closures = listCons((Value *)arg0, (List *)arity_14->closures);
incRef((Value *)rslt1);
arity_14->closures = listCons((Value *)rslt1, (List *)arity_14->closures);
Function *fn_519 = malloc_function(1);
fn_519->type = 3;
fn_519->name = "anon";
fn_519->arityCount = 1;
fn_519->arities[0] = arity_14;
Value *rslt15 = protoFnImpl_194(empty_list, rslt13, (Value *)fn_519);
incRef(rslt15);
cond7 = rslt15;
decRef(rslt13);
my_free(rslt13);
decRef((Value *)fn_519);
my_free((Value *)fn_519);
decRef(rslt15);
my_free(rslt15);
} else {
decRef(rslt12);
my_free(rslt12);
List *varArgs8 = empty_list;
incRef((Value *)var_121);
varArgs8 = (List *)listCons((Value *)var_121, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_507(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_194(empty_list, rslt1, rslt9);
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
decRef((Value *)fn_513);
my_free((Value *)fn_513);
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
Function fn_511 = {3, -1, "comprehend", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_512}}};

Value *var_220 = (Value *)&fn_511;

// --------- list-concat --------------
Function fn_521;
Value *arityImpl_522(List *closures, Value *arg0) {
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
Function fn_521 = {3, -1, "list-concat", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_522}}};


// --------- list=* --------------
Function fn_524;

// --------- anon --------------
Function fn_526;
Value *arityImpl_527(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_350(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- anon main body --------------
Function fn_526 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_527}}};

Value *arityImpl_525(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt4 = protoFnImpl_350(empty_list, arg0);
Value *rslt5 = protoFnImpl_306(empty_list, rslt4);
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
Value *rslt7 = protoFnImpl_252(empty_list, arg0, (Value *)&fn_526);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)(Value *)&fn_428);
varArgs8 = (List *)listCons((Value *)(Value *)&fn_428, varArgs8);
Value *rslt9 = arityImpl_238(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = arityImpl_420(empty_list, rslt9);
decRef(rslt7);
my_free(rslt7);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_252(empty_list, arg0, (Value *)&protoFn_353);
Value *rslt2 = arityImpl_525(closures, rslt1);
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
Function fn_524 = {3, -1, "list=*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_525}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_48 = {1, -1, 1,"("};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_49 = {1, -1, 2,", "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_50 = {1, -1, 1,")"};

// --------- crush_impl --------------
Function fn_529;

// --------- anon --------------
Function fn_531;
Value *arityImpl_532(List *closures, Value *arg0, Value *arg1) {
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
Value *rslt6 = arityImpl_381(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
decRef(rslt4);
my_free(rslt4);
decRef(rslt6);
my_free(rslt6);
return(rslt6);
};

Value *arityImpl_530(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_133(empty_list, arg0);
Value *rslt1 = arityImpl_130(empty_list, arg0);
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
arity_6->fn = arityImpl_532;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_531 = malloc_function(1);
fn_531->type = 3;
fn_531->name = "anon";
fn_531->arityCount = 1;
fn_531->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_331(empty_list, rslt0, rslt5, (Value *)fn_531);
incRef(rslt7);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt5);
my_free(rslt5);
decRef((Value *)fn_531);
my_free((Value *)fn_531);
decRef(rslt7);
my_free(rslt7);
return(rslt7);
};


// --------- crush_impl main body --------------
Function fn_529 = {3, -1, "crush_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_530}}};


// --------- traverse_impl --------------
Function fn_533;
Value *arityImpl_534(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_252(empty_list, arg0, arg1);
Value *rslt1 = protoFnImpl_350(empty_list, rslt0);
Value *rslt2 = protoFnImpl_225(empty_list, rslt1, (Value *)&fn_243);
Value *rslt3 = protoFnImpl_235(empty_list, rslt2, rslt0);
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
Function fn_533 = {3, -1, "traverse_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_534}}};


// --------- =*_impl --------------
Function fn_535;
Value *arityImpl_536(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_91(empty_list, arg0);
Value *rslt5 = arityImpl_91(empty_list, arg1);
Value *rslt6 = arityImpl_429(empty_list, rslt4, rslt5);
Value *rslt7 = arityImpl_420(empty_list, rslt6);
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
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt8 = protoFnImpl_321(empty_list, arg0);
Value *rslt9 = protoFnImpl_321(empty_list, arg1);
Value *rslt10 = arityImpl_104(empty_list, rslt8, rslt9);
Value *rslt11 = arityImpl_420(empty_list, rslt10);
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
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt11);
my_free(rslt11);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_525(empty_list, rslt2);
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
Function fn_535 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_536}}};


// --------- string-list_impl --------------
Function fn_537;
Value *arityImpl_538(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_48);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_48, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_276(empty_list, arg0, (Value *)&_str_49);
Value *rslt3 = protoFnImpl_194(empty_list, rslt2, (Value *)&protoFn_261);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_50, varArgs4);
Value *rslt5 = arityImpl_244(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_381(empty_list, (Value *)varArgs6);
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
Function fn_537 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_538}}};


// --------- empty?_impl --------------
Function fn_539;
Value *arityImpl_540(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_127(empty_list, arg0);
Value *rslt1 = arityImpl_104(empty_list, (Value *)&_num_12, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_539 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_540}}};


// --------- empty_impl --------------
Function fn_541;
Value *arityImpl_542(List *closures, Value *arg0) {
incRef(var_121);
return(var_121);
};


// --------- empty_impl main body --------------
Function fn_541 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_542}}};


// --------- conj_impl --------------
Function fn_543;
Value *arityImpl_544(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_124(empty_list, arg1, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- conj_impl main body --------------
Function fn_543 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_544}}};


// --------- count_impl --------------
Function fn_545;
Value *arityImpl_546(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_127(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_545 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_546}}};


// --------- reduce_impl --------------
Function fn_547;
Value *arityImpl_548(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt10 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg0);
Value *rslt2 = protoFnImpl_355(empty_list, arg0);
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
Value *rslt9 = protoFnImpl_306(empty_list, rslt2);
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
Value *rslt8 = protoFnImpl_331(empty_list, rslt2, rslt6, arg2);
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


// --------- reduce_impl main body --------------
Function fn_547 = {3, -1, "reduce_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_548}}};


// --------- seq?_impl --------------
Function fn_549;
Value *arityImpl_550(List *closures, Value *arg0) {
incRef(var_67);
return(var_67);
};


// --------- seq?_impl main body --------------
Function fn_549 = {3, -1, "seq?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_550}}};


// --------- seq_impl --------------
Function fn_551;
Value *arityImpl_552(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_551 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_552}}};


// --------- first_impl --------------
Function fn_553;
Value *arityImpl_554(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_130(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- first_impl main body --------------
Function fn_553 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_554}}};


// --------- rest_impl --------------
Function fn_555;
Value *arityImpl_556(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_133(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_555 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_556}}};


// --------- zero_impl --------------
Function fn_557;
Value *arityImpl_558(List *closures, Value *arg0) {
incRef(var_121);
return(var_121);
};


// --------- zero_impl main body --------------
Function fn_557 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_558}}};


// --------- comp*_impl --------------
Function fn_559;
Value *arityImpl_560(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_124(empty_list, arg0, arg1);
Value *rslt1 = arityImpl_522(empty_list, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_559 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_560}}};


// --------- map_impl --------------
Function fn_561;
Value *arityImpl_562(List *closures, Value *arg0, Value *arg1) {
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
Function fn_561 = {3, -1, "map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_562}}};


// --------- wrap_impl --------------
Function fn_563;
Value *arityImpl_564(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- wrap_impl main body --------------
Function fn_563 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_564}}};


// --------- flat-map_impl --------------
Function fn_565;
Value *arityImpl_566(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_252(empty_list, arg0, arg1);
Value *cond1;
Value *rslt5 = protoFnImpl_306(empty_list, rslt0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_121);
cond1 = var_121;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt2 = arityImpl_130(empty_list, rslt0);
Value *rslt3 = arityImpl_133(empty_list, rslt0);
Value *rslt4 = protoFnImpl_378(empty_list, rslt2, rslt3);
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
Function fn_565 = {3, -1, "flat-map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_566}}};


// --------- some --------------
Function fn_567;
Value *arityImpl_568(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg0);
decRef(rslt3);
my_free(rslt3);

if (isTrue(rslt3)) {
decRef(rslt3);
my_free(rslt3);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt3);
my_free(rslt3);
Value *rslt4 = protoFnImpl_350(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_355(empty_list, arg0);
Value *rslt2 = arityImpl_568(closures, rslt1, arg1);
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
Function fn_567 = {3, -1, "some", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_568}}};


// --------- inc --------------
Function fn_570;
Value *arityImpl_571(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_110(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- inc main body --------------
Function fn_570 = {3, -1, "inc", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_571}}};


// --------- + --------------
Function fn_573;
Value *arityImpl_574(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_306(empty_list, arg0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt2);
my_free(rslt2);
Value *rslt1 = protoFnImpl_331(empty_list, arg0, (Value *)&_num_12, (Value *)&fn_109);
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
Function fn_573 = {3, -1, "+", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_574}}};


// --------- * --------------
Function fn_576;
Value *arityImpl_577(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt2 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_331(empty_list, arg0, (Value *)&_num_1, (Value *)&fn_115);
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
Function fn_576 = {3, -1, "*", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_577}}};


// --------- dec --------------
Function fn_579;
Value *arityImpl_580(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_113(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- dec main body --------------
Function fn_579 = {3, -1, "dec", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_580}}};


// --------- - --------------
Function fn_582;
Value *arityImpl_583(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt6 = protoFnImpl_306(empty_list, arg0);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_350(empty_list, arg0);
Value *rslt2 = protoFnImpl_355(empty_list, arg0);
Value *cond3;
Value *rslt5 = protoFnImpl_306(empty_list, rslt2);
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
Value *rslt4 = protoFnImpl_331(empty_list, rslt2, rslt1, (Value *)&fn_112);
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
Function fn_582 = {3, -1, "-", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_583}}};

// forward declaration for 'maybe-val'
Value *var_585;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_51 = {1, -1, 9,"<nothing>"};

// --------- string-list_impl --------------
Function fn_586;
Value *arityImpl_587(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_51);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_51, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_586 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_587}}};

Value *protoImpl_588(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_589 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_588}}};


// --------- =*_impl --------------
Function fn_590;
Value *arityImpl_591(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_94(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_590 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_591}}};

Value *protoImpl_592(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_593 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_592}}};


// --------- zero_impl --------------
Function fn_594;
Value *arityImpl_595(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- zero_impl main body --------------
Function fn_594 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_595}}};

Value *protoImpl_596(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_597 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_596}}};


// --------- comp*_impl --------------
Function fn_598;
Value *arityImpl_599(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_355(empty_list, arg1);
Value *rslt3 = protoFnImpl_378(empty_list, rslt1, rslt2);
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
Function fn_598 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_599}}};

Value *protoImpl_600(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_601 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_600}}};


// --------- map_impl --------------
Function fn_602;
Value *arityImpl_603(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- map_impl main body --------------
Function fn_602 = {3, -1, "map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_603}}};

Value *protoImpl_604(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_605 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_604}}};


// --------- wrap_impl --------------
Function fn_606;
Value *arityImpl_607(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_585)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_585, arg1);
} else {
FnArity *arity0 = findFnArity(var_585, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_585)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_606 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_607}}};

Value *protoImpl_608(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_609 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_608}}};


// --------- apply*_impl --------------
Function fn_610;
Value *arityImpl_611(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- apply*_impl main body --------------
Function fn_610 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_611}}};

Value *protoImpl_612(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_613 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_612}}};


// --------- flatten_impl --------------
Function fn_614;
Value *arityImpl_615(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- flatten_impl main body --------------
Function fn_614 = {3, -1, "flatten_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_615}}};

Value *protoImpl_616(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_617 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_616}}};


// --------- flat-map_impl --------------
Function fn_618;
Value *arityImpl_619(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- flat-map_impl main body --------------
Function fn_618 = {3, -1, "flat-map_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_619}}};

Value *protoImpl_620(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_621 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_620}}};

ReifiedVal reified_622 = {14, -1, 9, {(Value *)&fn_586, (Value *)&fn_590, (Value *)&fn_594, (Value *)&fn_598, (Value *)&fn_602, (Value *)&fn_606, (Value *)&fn_610, (Value *)&fn_614, (Value *)&fn_618}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_52 = {1, -1, 7,"<maybe "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_53 = {1, -1, 9,"maybe-val"};
Number _num_14 = {2, -1, 16};

// --------- instance?_impl --------------
Function fn_624;
Value *arityImpl_625(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_91(empty_list, arg1);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_14, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_624 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_625}}};

Value *protoImpl_626(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_627 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_626}}};


// --------- invoke_impl --------------
Function fn_628;

// --------- string-list_impl --------------
Function fn_630;
Value *arityImpl_631(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_52, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_480(empty_list, arg0);
Value *rslt3 = protoFnImpl_264(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_46, varArgs4);
Value *rslt5 = arityImpl_244(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_381(empty_list, (Value *)varArgs6);
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
Function fn_630 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_631}}};

Value *protoImpl_632(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_633 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_632}}};


// --------- =*_impl --------------
Function fn_634;
Value *arityImpl_635(List *closures, Value *arg0, Value *arg1) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt4 = arityImpl_94(empty_list, arg0, arg1);
Value *rslt5 = arityImpl_420(empty_list, rslt4);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_68);
cond0 = var_68;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt2 = protoFnImpl_480(empty_list, arg1);
Value *rslt3 = arityImpl_429(empty_list, val1, rslt2);
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

Value *protoImpl_636(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_637 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_636}}};


// --------- zero_impl --------------
Function fn_638;
Value *arityImpl_639(List *closures, Value *arg0) {
incRef((Value *)&reified_622);
return((Value *)&reified_622);
};


// --------- zero_impl main body --------------
Function fn_638 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_639}}};

Value *protoImpl_640(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_641 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_640}}};


// --------- comp*_impl --------------
Function fn_642;
Value *arityImpl_643(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- comp*_impl main body --------------
Function fn_642 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_643}}};

Value *protoImpl_644(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_645 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_644}}};


// --------- map_impl --------------
Function fn_646;
Value *arityImpl_647(List *closures, Value *arg0, Value *arg1) {
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
if((var_585)->type != 3) {
rslt8 = protoFnImpl_10(empty_list, var_585, rslt4);
} else {
FnArity *arity5 = findFnArity(var_585, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_585)->name);
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

Value *protoImpl_648(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_649 = {3, -1, "map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_648}}};


// --------- wrap_impl --------------
Function fn_650;
Value *arityImpl_651(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_585)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_585, arg1);
} else {
FnArity *arity0 = findFnArity(var_585, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_585)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_650 = {3, -1, "wrap_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_651}}};

Value *protoImpl_652(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_653 = {3, -1, "wrap", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_652}}};


// --------- apply*_impl --------------
Function fn_654;
Value *arityImpl_655(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&reified_622);
varArgs9 = (List *)listCons((Value *)(Value *)&reified_622, varArgs9);
incRef((Value *)(Value *)&fn_428);
varArgs9 = (List *)listCons((Value *)(Value *)&fn_428, varArgs9);
Value *rslt10 = arityImpl_507(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
Value *rslt11 = arityImpl_568(empty_list, arg1, rslt10);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
incRef((Value *)&reified_622);
cond0 = (Value *)&reified_622;
} else {
decRef(rslt11);
my_free(rslt11);
Value *rslt1 = protoFnImpl_480(empty_list, arg0);
Value *rslt2 = protoFnImpl_252(empty_list, arg1, (Value *)&protoFn_478);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)rslt1);
varArgs3 = (List *)listCons((Value *)rslt1, varArgs3);
Value *rslt4 = arityImpl_238(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt8;
if((var_585)->type != 3) {
rslt8 = protoFnImpl_10(empty_list, var_585, rslt4);
} else {
FnArity *arity5 = findFnArity(var_585, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_585)->name);
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
Function fn_654 = {3, -1, "apply*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_655}}};

Value *protoImpl_656(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_657 = {3, -1, "apply*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_656}}};


// --------- flatten_impl --------------
Function fn_658;
Value *arityImpl_659(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_660(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_661 = {3, -1, "flatten", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_660}}};


// --------- flat-map_impl --------------
Function fn_662;
Value *arityImpl_663(List *closures, Value *arg0, Value *arg1) {
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

Value *protoImpl_664(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_665 = {3, -1, "flat-map", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_664}}};


// --------- type-name_impl --------------
Function fn_666;
Value *arityImpl_667(List *closures, Value *arg0) {
incRef((Value *)&_str_53);
return((Value *)&_str_53);
};


// --------- type-name_impl main body --------------
Function fn_666 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_667}}};

Value *protoImpl_668(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_669 = {3, -1, "type-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_668}}};


// --------- .v_impl --------------
Function fn_670;
Value *arityImpl_671(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_672(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_673 = {3, -1, ".v", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_672}}};

Value *arityImpl_629(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_635;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_634 = malloc_function(1);
fn_634->type = 3;
fn_634->name = "=*_impl";
fn_634->arityCount = 1;
fn_634->arities[0] = arity_1;
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_647;
incRef((Value *)arg1);
arity_4->closures = listCons((Value *)arg1, (List *)arity_4->closures);
Function *fn_646 = malloc_function(1);
fn_646->type = 3;
fn_646->name = "map_impl";
fn_646->arityCount = 1;
fn_646->arities[0] = arity_4;
FnArity *arity_7 = malloc_fnArity();
arity_7->type = 8;
arity_7->count = 1;
arity_7->closures = empty_list;
arity_7->variadic = 0;
arity_7->fn = arityImpl_659;
incRef((Value *)arg1);
arity_7->closures = listCons((Value *)arg1, (List *)arity_7->closures);
Function *fn_658 = malloc_function(1);
fn_658->type = 3;
fn_658->name = "flatten_impl";
fn_658->arityCount = 1;
fn_658->arities[0] = arity_7;
FnArity *arity_8 = malloc_fnArity();
arity_8->type = 8;
arity_8->count = 2;
arity_8->closures = empty_list;
arity_8->variadic = 0;
arity_8->fn = arityImpl_663;
incRef((Value *)arg1);
arity_8->closures = listCons((Value *)arg1, (List *)arity_8->closures);
Function *fn_662 = malloc_function(1);
fn_662->type = 3;
fn_662->name = "flat-map_impl";
fn_662->arityCount = 1;
fn_662->arities[0] = arity_8;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = 8;
arity_10->count = 1;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_671;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_670 = malloc_function(1);
fn_670->type = 3;
fn_670->name = ".v_impl";
fn_670->arityCount = 1;
fn_670->arities[0] = arity_10;
Value *reified_11 = (Value *)malloc_reified(11);
((ReifiedVal *)reified_11)->type = 16;
((ReifiedVal *)reified_11)->implCount = 11;
((ReifiedVal *)reified_11)->impls[0] = (Value *)&fn_630;
incRef((Value *)&fn_630);
((ReifiedVal *)reified_11)->impls[1] = (Value *)fn_634;
incRef((Value *)fn_634);
((ReifiedVal *)reified_11)->impls[2] = (Value *)&fn_638;
incRef((Value *)&fn_638);
((ReifiedVal *)reified_11)->impls[3] = (Value *)&fn_642;
incRef((Value *)&fn_642);
((ReifiedVal *)reified_11)->impls[4] = (Value *)fn_646;
incRef((Value *)fn_646);
((ReifiedVal *)reified_11)->impls[5] = (Value *)&fn_650;
incRef((Value *)&fn_650);
((ReifiedVal *)reified_11)->impls[6] = (Value *)&fn_654;
incRef((Value *)&fn_654);
((ReifiedVal *)reified_11)->impls[7] = (Value *)fn_658;
incRef((Value *)fn_658);
((ReifiedVal *)reified_11)->impls[8] = (Value *)fn_662;
incRef((Value *)fn_662);
((ReifiedVal *)reified_11)->impls[9] = (Value *)&fn_666;
incRef((Value *)&fn_666);
((ReifiedVal *)reified_11)->impls[10] = (Value *)fn_670;
incRef((Value *)fn_670);
incRef(reified_11);
decRef((Value *)fn_634);
my_free((Value *)fn_634);
decRef((Value *)fn_646);
my_free((Value *)fn_646);
decRef((Value *)fn_658);
my_free((Value *)fn_658);
decRef((Value *)fn_662);
my_free((Value *)fn_662);
decRef((Value *)fn_670);
my_free((Value *)fn_670);
decRef(reified_11);
my_free(reified_11);
return(reified_11);
};


// --------- invoke_impl main body --------------
Function fn_628 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_629}}};

Value *protoImpl_674(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_675 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_674}}};

ReifiedVal reified_676 = {15, -1, 2, {(Value *)&fn_624, (Value *)&fn_628}};
Value *var_585 = (Value *)&reified_676;
SubString _kw_4 = {5, -1, 13, 0, ":nothing-here"};

// --------- invoke_impl --------------
Function fn_677;
Value *arityImpl_678(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_585)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_585, arg1);
} else {
FnArity *arity0 = findFnArity(var_585, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_585)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- invoke_impl main body --------------
Function fn_677 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_678}}};

Value *protoImpl_679(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_680 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_679}}};


// --------- instance?_impl --------------
Function fn_681;
Value *arityImpl_682(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_188(empty_list, var_585, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- instance?_impl main body --------------
Function fn_681 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_682}}};

Value *protoImpl_683(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_684 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_683}}};


// --------- zero_impl --------------
Function fn_685;
Value *arityImpl_686(List *closures, Value *arg0) {
incRef((Value *)&reified_622);
return((Value *)&reified_622);
};


// --------- zero_impl main body --------------
Function fn_685 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_686}}};

Value *protoImpl_687(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_688 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_687}}};


// --------- comp*_impl --------------
Function fn_689;
Value *arityImpl_690(List *closures, Value *arg0, Value *arg1) {
incRef((Value *)&_kw_4);
return((Value *)&_kw_4);
};


// --------- comp*_impl main body --------------
Function fn_689 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_690}}};

Value *protoImpl_691(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_692 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_691}}};

ReifiedVal reified_693 = {17, -1, 4, {(Value *)&fn_677, (Value *)&fn_681, (Value *)&fn_685, (Value *)&fn_689}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_54 = {1, -1, 0,""};

// --------- =*_impl --------------
Function fn_695;
Value *arityImpl_696(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_145(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_695 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_696}}};


// --------- empty?_impl --------------
Function fn_697;
Value *arityImpl_698(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_142(empty_list, arg0);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_12, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_697 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_698}}};


// --------- empty_impl --------------
Function fn_699;
Value *arityImpl_700(List *closures, Value *arg0) {
incRef((Value *)&_str_54);
return((Value *)&_str_54);
};


// --------- empty_impl main body --------------
Function fn_699 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_700}}};


// --------- count_impl --------------
Function fn_701;
Value *arityImpl_702(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_142(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_701 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_702}}};


// --------- conj_impl --------------
Function fn_703;
Value *arityImpl_704(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, (Value *)&protoFn_261);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_380);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_380, varArgs3);
Value *rslt4 = arityImpl_238(empty_list, (Value *)varArgs3);
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
Function fn_703 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_704}}};


// --------- reduce_impl --------------
Function fn_705;
Value *arityImpl_706(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = protoFnImpl_331(empty_list, rslt0, arg1, arg2);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- reduce_impl main body --------------
Function fn_705 = {3, -1, "reduce_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_706}}};


// --------- seq_impl --------------
Function fn_707;
Value *arityImpl_708(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_429(empty_list, arg0, (Value *)&_str_54);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_98(empty_list, arg0, (Value *)&_num_12, (Value *)&_num_1);
Value *rslt2 = arityImpl_97(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_345(empty_list, rslt2);
Value *rslt4 = arityImpl_124(empty_list, rslt1, rslt3);
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
Value *rslt6 = arityImpl_429(empty_list, arg0, (Value *)&_str_54);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&reified_622);
cond0 = (Value *)&reified_622;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_98(empty_list, arg0, (Value *)&_num_12, (Value *)&_num_1);
Value *rslt5;
if(((Value *)&reified_693)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, (Value *)&reified_693, rslt1);
} else {
FnArity *arity2 = findFnArity((Value *)&reified_693, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&reified_693)->name);
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
Value *rslt0 = arityImpl_97(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_711 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_712}}};


// --------- string-list_impl --------------
Function fn_713;
Value *arityImpl_714(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_713 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_714}}};


// --------- comp*_impl --------------
Function fn_715;

// --------- anon --------------
Function fn_717;
Value *arityImpl_718(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_142(empty_list, arg1);
Value *rslt1 = arityImpl_110(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_717 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_718}}};


// --------- anon --------------
Function fn_719;
Value *arityImpl_720(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_154(empty_list, val0, arg0);
incRef((Value *)&_num_12);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_12);
};

Value *arityImpl_716(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_273(empty_list, arg1);
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
Value *rslt1 = arityImpl_124(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, (Value *)&protoFn_261);
Value *rslt4 = protoFnImpl_331(empty_list, rslt2, (Value *)&_num_12, (Value *)&fn_717);
Value *rslt5 = arityImpl_151(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_720;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_719 = malloc_function(1);
fn_719->type = 3;
fn_719->name = "anon";
fn_719->arityCount = 1;
fn_719->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_252(empty_list, rslt2, (Value *)fn_719);
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
decRef((Value *)fn_719);
my_free((Value *)fn_719);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_715 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_716}}};


// --------- sha1_impl --------------
Function fn_721;
Value *arityImpl_722(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
String *strVal = (String *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)strVal->buffer, strVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_721 = {3, -1, "sha1_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_722}}};


// --------- string-list_impl --------------
Function fn_723;
Value *arityImpl_724(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_723 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_724}}};


// --------- =*_impl --------------
Function fn_725;
Value *arityImpl_726(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_145(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_725 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_726}}};


// --------- empty?_impl --------------
Function fn_727;
Value *arityImpl_728(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_142(empty_list, arg0);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_12, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_727 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_728}}};


// --------- empty_impl --------------
Function fn_729;
Value *arityImpl_730(List *closures, Value *arg0) {
incRef((Value *)&_str_54);
return((Value *)&_str_54);
};


// --------- empty_impl main body --------------
Function fn_729 = {3, -1, "empty_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_730}}};


// --------- count_impl --------------
Function fn_731;
Value *arityImpl_732(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_142(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_731 = {3, -1, "count_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_732}}};


// --------- conj_impl --------------
Function fn_733;
Value *arityImpl_734(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_244(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, (Value *)&protoFn_261);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)(Value *)&fn_380);
varArgs3 = (List *)listCons((Value *)(Value *)&fn_380, varArgs3);
Value *rslt4 = arityImpl_238(empty_list, (Value *)varArgs3);
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
Function fn_733 = {3, -1, "conj_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_734}}};


// --------- reduce_impl --------------
Function fn_735;
Value *arityImpl_736(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = protoFnImpl_331(empty_list, rslt0, arg1, arg2);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- reduce_impl main body --------------
Function fn_735 = {3, -1, "reduce_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_736}}};


// --------- seq_impl --------------
Function fn_737;
Value *arityImpl_738(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_429(empty_list, arg0, (Value *)&_str_54);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_98(empty_list, arg0, (Value *)&_num_12, (Value *)&_num_1);
Value *rslt2 = arityImpl_97(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_345(empty_list, rslt2);
Value *rslt4 = arityImpl_124(empty_list, rslt1, rslt3);
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
Function fn_737 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_738}}};


// --------- first_impl --------------
Function fn_739;
Value *arityImpl_740(List *closures, Value *arg0) {
Value *cond0;
Value *rslt6 = arityImpl_429(empty_list, arg0, (Value *)&_str_54);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef((Value *)&reified_622);
cond0 = (Value *)&reified_622;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_98(empty_list, arg0, (Value *)&_num_12, (Value *)&_num_1);
Value *rslt5;
if(((Value *)&reified_693)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, (Value *)&reified_693, rslt1);
} else {
FnArity *arity2 = findFnArity((Value *)&reified_693, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&reified_693)->name);
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
Function fn_739 = {3, -1, "first_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_740}}};


// --------- rest_impl --------------
Function fn_741;
Value *arityImpl_742(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_97(empty_list, arg0, (Value *)&_num_1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_741 = {3, -1, "rest_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_742}}};


// --------- comp*_impl --------------
Function fn_743;

// --------- anon --------------
Function fn_745;
Value *arityImpl_746(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_142(empty_list, arg1);
Value *rslt1 = arityImpl_110(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_745 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_746}}};


// --------- anon --------------
Function fn_747;
Value *arityImpl_748(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_154(empty_list, val0, arg0);
incRef((Value *)&_num_12);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_12);
};

Value *arityImpl_744(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_273(empty_list, arg1);
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
Value *rslt1 = arityImpl_124(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_194(empty_list, rslt1, (Value *)&protoFn_261);
Value *rslt4 = protoFnImpl_331(empty_list, rslt2, (Value *)&_num_12, (Value *)&fn_745);
Value *rslt5 = arityImpl_151(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_748;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_747 = malloc_function(1);
fn_747->type = 3;
fn_747->name = "anon";
fn_747->arityCount = 1;
fn_747->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_252(empty_list, rslt2, (Value *)fn_747);
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
decRef((Value *)fn_747);
my_free((Value *)fn_747);
decRef(rslt7);
my_free(rslt7);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_743 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_744}}};


// --------- sha1_impl --------------
Function fn_749;
Value *arityImpl_750(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_749 = {3, -1, "sha1_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_750}}};


// --------- str --------------
Function fn_751;

// --------- anon --------------
Function fn_753;
Value *arityImpl_754(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_142(empty_list, arg1);
Value *rslt1 = arityImpl_110(empty_list, arg0, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- anon main body --------------
Function fn_753 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_754}}};


// --------- anon --------------
Function fn_755;
Value *arityImpl_756(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_154(empty_list, val0, arg0);
incRef((Value *)&_num_12);
decRef(rslt1);
my_free(rslt1);
return((Value *)&_num_12);
};

Value *arityImpl_752(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *cond0;
Value *rslt7 = protoFnImpl_306(empty_list, arg0);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef((Value *)&_str_54);
cond0 = (Value *)&_str_54;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_194(empty_list, arg0, (Value *)&protoFn_261);
Value *rslt3 = protoFnImpl_331(empty_list, rslt1, (Value *)&_num_12, (Value *)&fn_753);
Value *rslt4 = arityImpl_151(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_756;
incRef((Value *)rslt4);
arity_5->closures = listCons((Value *)rslt4, (List *)arity_5->closures);
Function *fn_755 = malloc_function(1);
fn_755->type = 3;
fn_755->name = "anon";
fn_755->arityCount = 1;
fn_755->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_252(empty_list, rslt1, (Value *)fn_755);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt3);
my_free(rslt3);
decRef(rslt4);
my_free(rslt4);
decRef((Value *)fn_755);
my_free((Value *)fn_755);
decRef(rslt6);
my_free(rslt6);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- str main body --------------
Function fn_751 = {3, -1, "str", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_752}}};


// --------- take --------------
Function fn_758;
Value *arityImpl_759(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt7 = arityImpl_429(empty_list, (Value *)&_num_12, arg1);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_350(empty_list, arg0);
Value *rslt2 = protoFnImpl_355(empty_list, arg0);
Value *rslt3 = arityImpl_580(empty_list, arg1);
Value *rslt4 = arityImpl_759(closures, rslt2, rslt3);
Value *rslt5 = arityImpl_124(empty_list, rslt1, rslt4);
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
Function fn_758 = {3, -1, "take", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_759}}};


// --------- drop --------------
Function fn_761;
Value *arityImpl_762(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_433(empty_list, arg1, (Value *)&_num_1);
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
Value *rslt1 = protoFnImpl_355(empty_list, arg0);
Value *rslt2 = arityImpl_580(empty_list, arg1);
Value *rslt3 = arityImpl_762(closures, rslt1, rslt2);
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
Function fn_761 = {3, -1, "drop", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_762}}};


// --------- split --------------
Function fn_764;
Value *arityImpl_765(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt6 = protoFnImpl_306(empty_list, arg0);
Value *rslt7 = arityImpl_433(empty_list, arg1, (Value *)&_num_1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_426(empty_list, (Value *)varArgs8);
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
Value *rslt10 = arityImpl_451(empty_list, arg2);
List *varArgs11 = empty_list;
incRef((Value *)arg0);
varArgs11 = (List *)listCons((Value *)arg0, varArgs11);
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
Value *rslt12 = arityImpl_244(empty_list, (Value *)varArgs11);
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
Value *rslt1 = protoFnImpl_355(empty_list, arg0);
Value *rslt2 = arityImpl_580(empty_list, arg1);
Value *rslt3 = protoFnImpl_350(empty_list, arg0);
Value *rslt4 = arityImpl_124(empty_list, rslt3, arg2);
Value *rslt5 = arityImpl_765(closures, rslt1, rslt2, rslt4);
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

Value *arityImpl_766(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if(((Value *)&fn_764)->type != 3) {
rslt3 = protoFnImpl_14(empty_list, (Value *)&fn_764, arg0, arg1, var_121);
} else {
FnArity *arity0 = findFnArity((Value *)&fn_764, 3);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType3 *fn2 = (FnType3 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg0, arg1, var_121);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_121);
varArgs1 = (List *)listCons(var_121, varArgs1);
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_764)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- split main body --------------
Function fn_764 = {3, -1, "split", 2, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_765}, &(FnArity){8, -1, 2, (List *)0, 0, arityImpl_766}}};


// --------- replace-at-nth --------------
Function fn_768;
Value *arityImpl_769(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt9 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt10 = protoFnImpl_321(empty_list, arg0);
Value *rslt11 = arityImpl_580(empty_list, rslt10);
Value *rslt12 = arityImpl_433(empty_list, rslt11, arg1);
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
Value *rslt1 = arityImpl_766(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_350(empty_list, rslt1);
List *varArgs3 = empty_list;
incRef((Value *)arg2);
varArgs3 = (List *)listCons((Value *)arg2, varArgs3);
Value *rslt4 = arityImpl_244(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_358(empty_list, rslt1);
Value *rslt6 = protoFnImpl_355(empty_list, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
incRef((Value *)rslt2);
varArgs7 = (List *)listCons((Value *)rslt2, varArgs7);
Value *rslt8 = arityImpl_381(empty_list, (Value *)varArgs7);
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
Function fn_768 = {3, -1, "replace-at-nth", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_769}}};


// --------- remove-nth --------------
Function fn_771;
Value *arityImpl_772(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt7 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt8 = protoFnImpl_321(empty_list, arg0);
Value *rslt9 = arityImpl_580(empty_list, rslt8);
Value *rslt10 = arityImpl_433(empty_list, rslt9, arg1);
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
Value *rslt1 = arityImpl_766(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_350(empty_list, rslt1);
Value *rslt3 = arityImpl_358(empty_list, rslt1);
Value *rslt4 = protoFnImpl_355(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
Value *rslt6 = arityImpl_381(empty_list, (Value *)varArgs5);
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
Function fn_771 = {3, -1, "remove-nth", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_772}}};


// --------- partition --------------
Function fn_774;
Value *arityImpl_775(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_321(empty_list, arg0);
Value *rslt6 = arityImpl_433(empty_list, rslt5, arg1);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_759(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_762(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_775(closures, rslt2, arg1);
Value *rslt4 = arityImpl_124(empty_list, rslt1, rslt3);
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
Function fn_774 = {3, -1, "partition", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_775}}};


// --------- partition-all --------------
Function fn_777;
Value *arityImpl_778(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_321(empty_list, arg0);
Value *rslt6 = arityImpl_433(empty_list, rslt5, arg1);
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
Value *rslt8 = arityImpl_244(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = arityImpl_759(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_762(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_778(closures, rslt2, arg1);
Value *rslt4 = arityImpl_124(empty_list, rslt1, rslt3);
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
Function fn_777 = {3, -1, "partition-all", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_778}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_55 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_780;
Value *arityImpl_781(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_306(empty_list, arg0);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_str_55);
varArgs6 = (List *)listCons((Value *)(Value *)&_str_55, varArgs6);
Value *rslt7 = arityImpl_290(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
Value *rslt8 = arityImpl_88(empty_list);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt9 = arityImpl_429(empty_list, arg1, (Value *)&_num_12);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_345(empty_list, arg0);
Value *rslt11 = protoFnImpl_350(empty_list, rslt10);
incRef(rslt11);
cond0 = rslt11;
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = protoFnImpl_355(empty_list, rslt1);
Value *rslt3 = arityImpl_580(empty_list, arg1);
Value *rslt4 = arityImpl_781(closures, rslt2, rslt3);
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

Value *arityImpl_782(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt6 = arityImpl_429(empty_list, arg1, (Value *)&_num_12);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = protoFnImpl_345(empty_list, arg0);
Value *rslt8 = protoFnImpl_350(empty_list, rslt7);
incRef(rslt8);
cond0 = rslt8;
decRef(rslt7);
my_free(rslt7);
decRef(rslt8);
my_free(rslt8);
} else {
decRef(rslt6);
my_free(rslt6);
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = protoFnImpl_355(empty_list, rslt1);
Value *rslt3 = arityImpl_580(empty_list, arg1);
Value *rslt4 = arityImpl_782(closures, rslt2, rslt3, arg2);
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
Function fn_780 = {3, -1, "nth", 2, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_781}, &(FnArity){8, -1, 3, (List *)0, 0, arityImpl_782}}};


// --------- last --------------
Function fn_784;
Value *arityImpl_785(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_321(empty_list, arg0);
Value *rslt1 = arityImpl_580(empty_list, rslt0);
Value *rslt2 = arityImpl_781(empty_list, arg0, rslt1);
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
Function fn_784 = {3, -1, "last", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_785}}};


// --------- butlast --------------
Function fn_787;
Value *arityImpl_788(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt6 = protoFnImpl_321(empty_list, arg0);
Value *rslt7 = arityImpl_429(empty_list, (Value *)&_num_1, rslt6);
decRef(rslt6);
my_free(rslt6);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt1 = protoFnImpl_350(empty_list, arg0);
Value *rslt2 = protoFnImpl_355(empty_list, arg0);
Value *rslt3 = arityImpl_788(closures, rslt2);
Value *rslt4 = arityImpl_124(empty_list, rslt1, rslt3);
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
Function fn_787 = {3, -1, "butlast", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_788}}};


// --------- map-assoc --------------
Function fn_790;
Value *arityImpl_791(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = arityImpl_273(empty_list, arg0);
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
Value *rslt7 = arityImpl_244(empty_list, (Value *)varArgs6);
decRef((Value *)varArgs6);
my_free((Value *)varArgs6);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
Value *rslt9 = arityImpl_244(empty_list, (Value *)varArgs8);
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
Value *rslt10 = arityImpl_130(empty_list, arg0);
Value *rslt11 = arityImpl_130(empty_list, rslt10);
Value *rslt12 = arityImpl_429(empty_list, rslt11, arg1);
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
Value *rslt14 = arityImpl_244(empty_list, (Value *)varArgs13);
decRef((Value *)varArgs13);
my_free((Value *)varArgs13);
Value *rslt15 = arityImpl_133(empty_list, arg0);
Value *rslt16 = arityImpl_124(empty_list, rslt14, rslt15);
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
Value *rslt1 = arityImpl_130(empty_list, arg0);
Value *rslt2 = arityImpl_133(empty_list, arg0);
Value *rslt3 = arityImpl_791(closures, rslt2, arg1, arg2);
Value *rslt4 = arityImpl_124(empty_list, rslt1, rslt3);
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
Function fn_790 = {3, -1, "map-assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_791}}};


// --------- map-get --------------
Function fn_793;
Value *arityImpl_794(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt3 = arityImpl_273(empty_list, arg0);
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
Value *rslt4 = arityImpl_130(empty_list, arg0);
Value *rslt5 = arityImpl_130(empty_list, rslt4);
Value *rslt6 = arityImpl_429(empty_list, rslt5, arg1);
decRef(rslt4);
my_free(rslt4);
decRef(rslt5);
my_free(rslt5);
decRef(rslt6);
my_free(rslt6);

if (isTrue(rslt6)) {
decRef(rslt6);
my_free(rslt6);
Value *rslt7 = arityImpl_130(empty_list, arg0);
Value *rslt8 = arityImpl_133(empty_list, rslt7);
Value *rslt9 = arityImpl_130(empty_list, rslt8);
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
Value *rslt1 = arityImpl_133(empty_list, arg0);
Value *rslt2 = arityImpl_794(closures, rslt1, arg1, arg2);
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
Function fn_793 = {3, -1, "map-get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_794}}};

SubString _kw_5 = {5, -1, 6, 0, ":hm-nf"};

// --------- hash-map= --------------
Function fn_796;
Value *arityImpl_797(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt13 = protoFnImpl_306(empty_list, arg0);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg0);
Value *rslt2 = protoFnImpl_350(empty_list, rslt1);
Value *rslt3 = protoFnImpl_355(empty_list, rslt1);
Value *rslt4 = protoFnImpl_350(empty_list, rslt3);
Value *cond5;
Value *rslt8 = arityImpl_429(empty_list, (Value *)&_kw_5, rslt2);
decRef(rslt8);
my_free(rslt8);

if (isTrue(rslt8)) {
decRef(rslt8);
my_free(rslt8);
incRef((Value *)&_num_12);
cond5 = (Value *)&_num_12;
} else {
decRef(rslt8);
my_free(rslt8);
Value *rslt9 = arityImpl_429(empty_list, (Value *)&_kw_5, rslt4);
decRef(rslt9);
my_free(rslt9);

if (isTrue(rslt9)) {
decRef(rslt9);
my_free(rslt9);
incRef((Value *)&_num_12);
cond5 = (Value *)&_num_12;
} else {
decRef(rslt9);
my_free(rslt9);
Value *rslt10 = protoFnImpl_402(empty_list, arg1, rslt2, (Value *)&_kw_5);
Value *rslt11 = arityImpl_429(empty_list, rslt4, rslt10);
Value *rslt12 = arityImpl_420(empty_list, rslt11);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);

if (isTrue(rslt12)) {
decRef(rslt12);
my_free(rslt12);
incRef((Value *)&_num_12);
cond5 = (Value *)&_num_12;
} else {
decRef(rslt12);
my_free(rslt12);
Value *rslt6 = protoFnImpl_355(empty_list, arg0);
Value *rslt7 = arityImpl_797(closures, rslt6, arg1);
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
Function fn_796 = {3, -1, "hash-map=", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_797}}};


BitmapIndexedNode emptyBMI = {BitmapIndexedType, -1, 0, 0};

BitmapIndexedNode *clone_BitmapIndexedNode(BitmapIndexedNode *node)
{
  int itemCount = __builtin_popcount(node->bitmap);
  int nodeSize = sizeof(BitmapIndexedNode) + sizeof(Value *) *
                 (itemCount * 2);
  BitmapIndexedNode *newNode = (BitmapIndexedNode *)my_malloc(nodeSize);
  newNode->type = BitmapIndexedType;
  newNode->refs = 1;
  newNode->bitmap = node->bitmap;
  for (int i = 0; i < itemCount * 2; i++) {
    if (node->array[i] != (Value *)0)
      incRef(node->array[i]);
    newNode->array[i] = node->array[i];
  }
  return(newNode);
}

Value *createNode(int shift,
                  int64_t key1hash, Value *key1, Value *val1,
                  int64_t key2hash, Value *key2, Value *val2)
{
  if (shift > 60) {
    fprintf(stderr, "Ran out of shift!!!!!!");
    abort();
  }
  int nodeSize = sizeof(BitmapIndexedNode) + sizeof(Value *) * 4;
  BitmapIndexedNode *newNode = (BitmapIndexedNode *)my_malloc(nodeSize);
  newNode->type = BitmapIndexedType;
  newNode->refs = 1;
  int key1bit = bitpos(key1hash, shift);
  int key2bit = bitpos(key2hash, shift);
  newNode->bitmap = key1bit || key2bit;
  if (key1bit < key2bit) {
    incRef(key1);
    incRef(val1);
    incRef(key2);
    incRef(val2);
    newNode->array[0] = key1;
    newNode->array[1] = val1;
    newNode->array[2] = key2;
    newNode->array[3] = val2;
  } else if (key1bit > key2bit) {
    incRef(key1);
    incRef(val1);
    incRef(key2);
    incRef(val2);
    newNode->array[0] = key2;
    newNode->array[1] = val2;
    newNode->array[2] = key1;
    newNode->array[3] = val1;
  } else {
    newNode->array[0] = (Value *)0;
    newNode->array [1] = createNode(shift + 5, key1hash, key1, val1,
                                               key2hash, key2, val2);
  }
  return((Value *)newNode);
}
Value *var_799 = (Value *)&emptyBMI;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_56 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_57 = {1, -1, 1,"{"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_58 = {1, -1, 1,"}"};

// --------- empty?_impl --------------
Function fn_800;
Value *arityImpl_801(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = protoFnImpl_321(empty_list, rslt0);
Value *rslt2 = arityImpl_429(empty_list, (Value *)&_num_12, rslt1);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- empty?_impl main body --------------
Function fn_800 = {3, -1, "empty?_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_801}}};


// --------- seq_impl --------------
Function fn_802;
Value *arityImpl_803(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_386(empty_list, arg0, var_121);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- seq_impl main body --------------
Function fn_802 = {3, -1, "seq_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_803}}};


// --------- string-list_impl --------------
Function fn_804;

// --------- anon --------------
Function fn_806;
Value *arityImpl_807(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_252(empty_list, arg0, (Value *)&protoFn_261);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_39);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_39, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_276(empty_list, rslt0, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_380);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_380, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
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
Function fn_806 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_807}}};

Value *arityImpl_805(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *cond1;
Value *rslt15 = arityImpl_273(empty_list, rslt0);
decRef(rslt15);
my_free(rslt15);

if (isTrue(rslt15)) {
decRef(rslt15);
my_free(rslt15);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_56);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_56, varArgs16);
Value *rslt17 = arityImpl_244(empty_list, (Value *)varArgs16);
decRef((Value *)varArgs16);
my_free((Value *)varArgs16);
incRef(rslt17);
cond1 = rslt17;
decRef(rslt17);
my_free(rslt17);
} else {
decRef(rslt15);
my_free(rslt15);
Value *rslt3 = protoFnImpl_252(empty_list, rslt0, (Value *)&fn_806);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_49);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_49, varArgs4);
Value *rslt5 = arityImpl_244(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = arityImpl_276(empty_list, rslt3, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)(Value *)&fn_380);
varArgs7 = (List *)listCons((Value *)(Value *)&fn_380, varArgs7);
Value *rslt8 = arityImpl_238(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs9 = (List *)listCons((Value *)(Value *)&_str_57, varArgs9);
Value *rslt10 = arityImpl_244(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_58, varArgs11);
Value *rslt12 = arityImpl_244(empty_list, (Value *)varArgs11);
decRef((Value *)varArgs11);
my_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)rslt12);
varArgs13 = (List *)listCons((Value *)rslt12, varArgs13);
incRef((Value *)rslt8);
varArgs13 = (List *)listCons((Value *)rslt8, varArgs13);
incRef((Value *)rslt10);
varArgs13 = (List *)listCons((Value *)rslt10, varArgs13);
Value *rslt14 = arityImpl_381(empty_list, (Value *)varArgs13);
decRef((Value *)varArgs13);
my_free((Value *)varArgs13);
incRef(rslt14);
cond1 = rslt14;
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
incRef(cond1);
decRef(rslt0);
my_free(rslt0);
decRef(cond1);
my_free(cond1);
return(cond1);
};


// --------- string-list_impl main body --------------
Function fn_804 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_805}}};


// --------- hash-seq_impl --------------
Function fn_808;
Value *arityImpl_809(List *closures, Value *arg0, Value *arg1) {

BitmapIndexedNode *node = (BitmapIndexedNode *)arg0;
int cnt = __builtin_popcount(node->bitmap);
List *seq = (List *)arg1;
for (int i = 0; i < cnt; i++) {
   if (node->array[2 * i] == (Value *)0) {
     seq = (List *)hashSeq(node->array[2 * i + 1], (Value *)seq);
   } else {
     List *pair = listCons(node->array[2 * i], listCons(node->array[2 * i + 1], empty_list));
     incRef((Value *)pair);
     incRef(node->array[2 * i]);
     incRef(node->array[2 * i + 1]);
     seq = listCons((Value *)pair, seq);
   }
}
return((Value *)seq);
};


// --------- hash-seq_impl main body --------------
Function fn_808 = {3, -1, "hash-seq_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_809}}};


// --------- assoc*_impl --------------
Function fn_810;
Value *arityImpl_811(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

BitmapIndexedNode *node = (BitmapIndexedNode *)arg0;
Value *key = arg1;
Value *val = arg2;
int64_t hash = ((Number *)arg3)->numVal;
int64_t shift = ((Number *)arg4)->numVal;

int bit = bitpos(hash, shift);
int idx = __builtin_popcount(node->bitmap & (bit - 1));
if (node->bitmap & bit) {
  // if the hash position is already filled
  Value *keyOrNull = node->array[2 * idx];
  Value *valOrNode = node->array[2 * idx + 1];
  if (keyOrNull == (Value *)0) {
    // There is no key in the position, so valOrNode is
    // pointer to a node.
    Value *n = assoc(valOrNode, key, val, arg3, arg4);
    if (n == valOrNode) {
      // the key was already associated with the value
      // so do nothing
      decRef(n);
      my_free(n);
      incRef(arg0);
      return(arg0);
    } else {
      // clone node and add n to it
      BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node);
      newNode->array[2 * idx + 1] = n;
      return((Value *)newNode);
    }
  } else if (equal(key, keyOrNull)) {
    // if the keyOrNull points to a value that is equal to key
/*
    if (equal(val, valOrNode)) {
      // if the valOrNode points to a value that is equal to val
      incRef(arg0);
      return(arg0);
    } else {
*/
      // create new hash-map with valOrNode replaced by val
      // clone node and add val to it
      BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node);
      incRef((Value *)val);
      newNode->array[2 * idx + 1] = val;
      return((Value *)newNode);
/*
    }
*/
  } else {
    // there is already a key/val pair at the position where key
    // would be placed. Extend tree a level
    int64_t existingKeyHash = ((Number *)sha1(keyOrNull))->numVal;
    if (existingKeyHash == hash) {
      // make & return HashCollisionNode
      fprintf(stderr, "Need to implement HashCollisionNode!\n");
      abort();
    } else {
      Value *newLeaf = createNode(shift + 5,
                                  existingKeyHash, keyOrNull, valOrNode,
                                  hash, key, val);
      BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node);
      newNode->array[2 * idx] = (Value *)0;
      newNode->array[2 * idx + 1] = newLeaf;
      return((Value *)newNode);
    }
  }
} else {
  // the position in the node is empty
  int n = __builtin_popcount(node->bitmap);
  if (n > 16) {
    fprintf(stderr, "Implement ArrayNode!!!!\n");
    abort();
    return((Value *)0);
  } else {
    int itemCount = n + 1;
    int nodeSize = sizeof(BitmapIndexedNode) + sizeof(Value *) *
                   (itemCount * 2);
    BitmapIndexedNode *newNode = (BitmapIndexedNode *)my_malloc(nodeSize);
    newNode->type = BitmapIndexedType;
    newNode->refs = 1;
    newNode->bitmap = node->bitmap | bit;
    incRef(key);
    incRef(val);
    for (int i = 0; i < idx * 2; i++) {
      if (node->array[i] != (Value *)0)
        incRef(node->array[i]);
      newNode->array[i] = node->array[i];
    }
    newNode->array[2 * idx] = key;
    newNode->array[2 * idx + 1] = val;
    for (int i = idx * 2; i < n * 2; i++) {
      if (node->array[i] != (Value *)0)
        incRef(node->array[i]);
      newNode->array[i + 2] = node->array[i];
    }
    return((Value *)newNode);
  }
}
};


// --------- assoc*_impl main body --------------
Function fn_810 = {3, -1, "assoc*_impl", 1, {&(FnArity){8, -1, 5, (List *)0, 0, arityImpl_811}}};


// --------- get_impl --------------
Function fn_812;
Value *arityImpl_813(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = arityImpl_794(empty_list, rslt0, arg1, arg2);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- get_impl main body --------------
Function fn_812 = {3, -1, "get_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_813}}};


// --------- keys_impl --------------
Function fn_814;
Value *arityImpl_815(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = protoFnImpl_252(empty_list, rslt0, (Value *)&protoFn_348);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- keys_impl main body --------------
Function fn_814 = {3, -1, "keys_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_815}}};


// --------- vals_impl --------------
Function fn_816;
Value *arityImpl_817(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_345(empty_list, arg0);
Value *rslt1 = protoFnImpl_252(empty_list, rslt0, (Value *)&fn_357);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- vals_impl main body --------------
Function fn_816 = {3, -1, "vals_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_817}}};


// --------- assoc_impl --------------
Function fn_818;
Value *arityImpl_819(List *closures, Value *arg0, Value *arg1, Value *arg2) {

return(assoc(arg0, arg1, arg2, sha1(arg1), numberValue(0)));
};


// --------- assoc_impl main body --------------
Function fn_818 = {3, -1, "assoc_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_819}}};

ProtoImpls *protoImpls_820;
Value *protoFnImpl_823(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_820);
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
FnArity protoFnArity_824 = {8, -1, 1, (List *)0, 0, protoFnImpl_823};
Function protoFn_821 = {3, -1, ".a-list", 1, {&protoFnArity_824}};

// forward declaration for 'HashMap'
Value *var_825;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_59 = {1, -1, 7,"HashMap"};
Number _num_15 = {2, -1, 19};

// --------- instance?_impl --------------
Function fn_826;
Value *arityImpl_827(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_91(empty_list, arg1);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_15, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_826 = {3, -1, "instance?_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_827}}};

Value *protoImpl_828(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_829 = {3, -1, "instance?", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_828}}};


// --------- invoke_impl --------------
Function fn_830;

// --------- seq_impl --------------
Function fn_832;
Value *arityImpl_833(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_834(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_835 = {3, -1, "seq", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_834}}};


// --------- first_impl --------------
Function fn_836;
Value *arityImpl_837(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_130(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_838(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_839 = {3, -1, "first", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_838}}};


// --------- rest_impl --------------
Function fn_840;
Value *arityImpl_841(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_133(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_842(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_843 = {3, -1, "rest", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_842}}};


// --------- =*_impl --------------
Function fn_844;
Value *arityImpl_845(List *closures, Value *arg0, Value *arg1) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt3 = protoFnImpl_321(empty_list, val1);
Value *rslt4 = protoFnImpl_345(empty_list, arg1);
Value *rslt5 = protoFnImpl_321(empty_list, rslt4);
Value *rslt6 = arityImpl_429(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_420(empty_list, rslt6);
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
incRef((Value *)&_num_12);
cond0 = (Value *)&_num_12;
} else {
decRef(rslt7);
my_free(rslt7);
Value *rslt2 = arityImpl_797(empty_list, val1, arg1);
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

Value *protoImpl_846(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_847 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_846}}};


// --------- string-list_impl --------------
Function fn_848;

// --------- anon --------------
Function fn_850;
Value *arityImpl_851(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_252(empty_list, arg0, (Value *)&protoFn_261);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_39);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_39, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
Value *rslt3 = arityImpl_276(empty_list, rslt0, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)(Value *)&fn_380);
varArgs4 = (List *)listCons((Value *)(Value *)&fn_380, varArgs4);
Value *rslt5 = arityImpl_238(empty_list, (Value *)varArgs4);
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
Function fn_850 = {3, -1, "anon", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_851}}};

Value *arityImpl_849(List *closures, Value *arg0) {
Value *val1 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt15 = arityImpl_273(empty_list, val1);
decRef(rslt15);
my_free(rslt15);

if (isTrue(rslt15)) {
decRef(rslt15);
my_free(rslt15);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_56);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_56, varArgs16);
Value *rslt17 = arityImpl_244(empty_list, (Value *)varArgs16);
decRef((Value *)varArgs16);
my_free((Value *)varArgs16);
incRef(rslt17);
cond0 = rslt17;
decRef(rslt17);
my_free(rslt17);
} else {
decRef(rslt15);
my_free(rslt15);
Value *rslt3 = protoFnImpl_252(empty_list, val1, (Value *)&fn_850);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_49);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_49, varArgs4);
Value *rslt5 = arityImpl_244(empty_list, (Value *)varArgs4);
decRef((Value *)varArgs4);
my_free((Value *)varArgs4);
Value *rslt6 = arityImpl_276(empty_list, rslt3, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)(Value *)&fn_380);
varArgs7 = (List *)listCons((Value *)(Value *)&fn_380, varArgs7);
Value *rslt8 = arityImpl_238(empty_list, (Value *)varArgs7);
decRef((Value *)varArgs7);
my_free((Value *)varArgs7);
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs9 = (List *)listCons((Value *)(Value *)&_str_57, varArgs9);
Value *rslt10 = arityImpl_244(empty_list, (Value *)varArgs9);
decRef((Value *)varArgs9);
my_free((Value *)varArgs9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_58, varArgs11);
Value *rslt12 = arityImpl_244(empty_list, (Value *)varArgs11);
decRef((Value *)varArgs11);
my_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)rslt12);
varArgs13 = (List *)listCons((Value *)rslt12, varArgs13);
incRef((Value *)rslt8);
varArgs13 = (List *)listCons((Value *)rslt8, varArgs13);
incRef((Value *)rslt10);
varArgs13 = (List *)listCons((Value *)rslt10, varArgs13);
Value *rslt14 = arityImpl_381(empty_list, (Value *)varArgs13);
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

Value *protoImpl_852(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_853 = {3, -1, "string-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_852}}};


// --------- empty?_impl --------------
Function fn_854;
Value *arityImpl_855(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_306(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_856(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_857 = {3, -1, "empty?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_856}}};


// --------- count_impl --------------
Function fn_858;
Value *arityImpl_859(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_321(empty_list, val0);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_860(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_861 = {3, -1, "count", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_860}}};


// --------- reduce_impl --------------
Function fn_862;
Value *arityImpl_863(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_331(empty_list, val0, arg1, arg2);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_864(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_865 = {3, -1, "reduce", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_864}}};


// --------- zero_impl --------------
Function fn_866;
Value *arityImpl_867(List *closures, Value *arg0) {
Value *rslt3;
if((var_825)->type != 3) {
rslt3 = protoFnImpl_10(empty_list, var_825, var_121);
} else {
FnArity *arity0 = findFnArity(var_825, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, var_121);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_121);
varArgs1 = (List *)listCons(var_121, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
decRef((Value *)varArgs1);
my_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_825)->name);
  abort();
}
}
incRef(rslt3);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};


// --------- zero_impl main body --------------
Function fn_866 = {3, -1, "zero_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_867}}};

Value *protoImpl_868(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_869 = {3, -1, "zero", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_868}}};


// --------- comp*_impl --------------
Function fn_870;

// --------- anon --------------
Function fn_872;

// --------- anon --------------
Function fn_874;
Value *arityImpl_875(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_781(empty_list, arg1, (Value *)&_num_12);
Value *rslt1 = arityImpl_781(empty_list, arg1, (Value *)&_num_1);
Value *rslt2 = protoFnImpl_396(empty_list, arg0, rslt0, rslt1);
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
Function fn_874 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_875}}};

Value *arityImpl_873(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = protoFnImpl_331(empty_list, rslt0, arg0, (Value *)&fn_874);
incRef(rslt2);
decRef(rslt0);
my_free(rslt0);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_872 = {3, -1, "anon", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_873}}};

Value *arityImpl_871(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg1);
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
Value *rslt2 = protoFnImpl_331(empty_list, arg1, arg0, (Value *)&fn_872);
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
Function fn_870 = {3, -1, "comp*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_871}}};

Value *protoImpl_876(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_877 = {3, -1, "comp*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_876}}};


// --------- assoc_impl --------------
Function fn_878;
Value *arityImpl_879(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_791(empty_list, val0, arg1, arg2);
Value *rslt5;
if((var_825)->type != 3) {
rslt5 = protoFnImpl_10(empty_list, var_825, rslt1);
} else {
FnArity *arity2 = findFnArity(var_825, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_825)->name);
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

Value *protoImpl_880(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_881 = {3, -1, "assoc", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_880}}};


// --------- get_impl --------------
Function fn_882;
Value *arityImpl_883(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = arityImpl_794(empty_list, val0, arg1, arg2);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_884(List *closures, Value *arg0, Value *arg1, Value *arg2) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[11])->arities[0];
Value *rval = ((FnType3 *)arityPtr->fn)(arityPtr->closures, arg0, arg1, arg2);
return(rval);
};

Function protoFn_885 = {3, -1, "get", 1, {&(FnArity){8, -1, 3, (List *)0, 0, protoImpl_884}}};


// --------- keys_impl --------------
Function fn_886;
Value *arityImpl_887(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_252(empty_list, val0, (Value *)&protoFn_348);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_888(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[12])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_889 = {3, -1, "keys", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_888}}};


// --------- vals_impl --------------
Function fn_890;
Value *arityImpl_891(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt1 = protoFnImpl_252(empty_list, val0, (Value *)&fn_357);
incRef(rslt1);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};

Value *protoImpl_892(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[13])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_893 = {3, -1, "vals", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_892}}};


// --------- type-name_impl --------------
Function fn_894;
Value *arityImpl_895(List *closures, Value *arg0) {
incRef((Value *)&_str_59);
return((Value *)&_str_59);
};


// --------- type-name_impl main body --------------
Function fn_894 = {3, -1, "type-name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_895}}};

Value *protoImpl_896(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[14])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_897 = {3, -1, "type-name", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_896}}};


// --------- .a-list_impl --------------
Function fn_898;
Value *arityImpl_899(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_900(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[15])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_901 = {3, -1, ".a-list", 1, {&(FnArity){8, -1, 1, (List *)0, 0, protoImpl_900}}};

Value *arityImpl_831(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = 8;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_833;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_832 = malloc_function(1);
fn_832->type = 3;
fn_832->name = "seq_impl";
fn_832->arityCount = 1;
fn_832->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_837;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_836 = malloc_function(1);
fn_836->type = 3;
fn_836->name = "first_impl";
fn_836->arityCount = 1;
fn_836->arities[0] = arity_1;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = 8;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_841;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_840 = malloc_function(1);
fn_840->type = 3;
fn_840->name = "rest_impl";
fn_840->arityCount = 1;
fn_840->arities[0] = arity_2;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_845;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_844 = malloc_function(1);
fn_844->type = 3;
fn_844->name = "=*_impl";
fn_844->arityCount = 1;
fn_844->arities[0] = arity_3;
FnArity *arity_4 = malloc_fnArity();
arity_4->type = 8;
arity_4->count = 1;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_849;
incRef((Value *)arg1);
arity_4->closures = listCons((Value *)arg1, (List *)arity_4->closures);
Function *fn_848 = malloc_function(1);
fn_848->type = 3;
fn_848->name = "string-list_impl";
fn_848->arityCount = 1;
fn_848->arities[0] = arity_4;
FnArity *arity_5 = malloc_fnArity();
arity_5->type = 8;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_855;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_854 = malloc_function(1);
fn_854->type = 3;
fn_854->name = "empty?_impl";
fn_854->arityCount = 1;
fn_854->arities[0] = arity_5;
FnArity *arity_6 = malloc_fnArity();
arity_6->type = 8;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_859;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_858 = malloc_function(1);
fn_858->type = 3;
fn_858->name = "count_impl";
fn_858->arityCount = 1;
fn_858->arities[0] = arity_6;
FnArity *arity_7 = malloc_fnArity();
arity_7->type = 8;
arity_7->count = 3;
arity_7->closures = empty_list;
arity_7->variadic = 0;
arity_7->fn = arityImpl_863;
incRef((Value *)arg1);
arity_7->closures = listCons((Value *)arg1, (List *)arity_7->closures);
Function *fn_862 = malloc_function(1);
fn_862->type = 3;
fn_862->name = "reduce_impl";
fn_862->arityCount = 1;
fn_862->arities[0] = arity_7;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = 8;
arity_10->count = 3;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_879;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_878 = malloc_function(1);
fn_878->type = 3;
fn_878->name = "assoc_impl";
fn_878->arityCount = 1;
fn_878->arities[0] = arity_10;
FnArity *arity_11 = malloc_fnArity();
arity_11->type = 8;
arity_11->count = 3;
arity_11->closures = empty_list;
arity_11->variadic = 0;
arity_11->fn = arityImpl_883;
incRef((Value *)arg1);
arity_11->closures = listCons((Value *)arg1, (List *)arity_11->closures);
Function *fn_882 = malloc_function(1);
fn_882->type = 3;
fn_882->name = "get_impl";
fn_882->arityCount = 1;
fn_882->arities[0] = arity_11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = 8;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_887;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_886 = malloc_function(1);
fn_886->type = 3;
fn_886->name = "keys_impl";
fn_886->arityCount = 1;
fn_886->arities[0] = arity_12;
FnArity *arity_13 = malloc_fnArity();
arity_13->type = 8;
arity_13->count = 1;
arity_13->closures = empty_list;
arity_13->variadic = 0;
arity_13->fn = arityImpl_891;
incRef((Value *)arg1);
arity_13->closures = listCons((Value *)arg1, (List *)arity_13->closures);
Function *fn_890 = malloc_function(1);
fn_890->type = 3;
fn_890->name = "vals_impl";
fn_890->arityCount = 1;
fn_890->arities[0] = arity_13;
FnArity *arity_15 = malloc_fnArity();
arity_15->type = 8;
arity_15->count = 1;
arity_15->closures = empty_list;
arity_15->variadic = 0;
arity_15->fn = arityImpl_899;
incRef((Value *)arg1);
arity_15->closures = listCons((Value *)arg1, (List *)arity_15->closures);
Function *fn_898 = malloc_function(1);
fn_898->type = 3;
fn_898->name = ".a-list_impl";
fn_898->arityCount = 1;
fn_898->arities[0] = arity_15;
Value *reified_16 = (Value *)malloc_reified(16);
((ReifiedVal *)reified_16)->type = 19;
((ReifiedVal *)reified_16)->implCount = 16;
((ReifiedVal *)reified_16)->impls[0] = (Value *)fn_832;
incRef((Value *)fn_832);
((ReifiedVal *)reified_16)->impls[1] = (Value *)fn_836;
incRef((Value *)fn_836);
((ReifiedVal *)reified_16)->impls[2] = (Value *)fn_840;
incRef((Value *)fn_840);
((ReifiedVal *)reified_16)->impls[3] = (Value *)fn_844;
incRef((Value *)fn_844);
((ReifiedVal *)reified_16)->impls[4] = (Value *)fn_848;
incRef((Value *)fn_848);
((ReifiedVal *)reified_16)->impls[5] = (Value *)fn_854;
incRef((Value *)fn_854);
((ReifiedVal *)reified_16)->impls[6] = (Value *)fn_858;
incRef((Value *)fn_858);
((ReifiedVal *)reified_16)->impls[7] = (Value *)fn_862;
incRef((Value *)fn_862);
((ReifiedVal *)reified_16)->impls[8] = (Value *)&fn_866;
incRef((Value *)&fn_866);
((ReifiedVal *)reified_16)->impls[9] = (Value *)&fn_870;
incRef((Value *)&fn_870);
((ReifiedVal *)reified_16)->impls[10] = (Value *)fn_878;
incRef((Value *)fn_878);
((ReifiedVal *)reified_16)->impls[11] = (Value *)fn_882;
incRef((Value *)fn_882);
((ReifiedVal *)reified_16)->impls[12] = (Value *)fn_886;
incRef((Value *)fn_886);
((ReifiedVal *)reified_16)->impls[13] = (Value *)fn_890;
incRef((Value *)fn_890);
((ReifiedVal *)reified_16)->impls[14] = (Value *)&fn_894;
incRef((Value *)&fn_894);
((ReifiedVal *)reified_16)->impls[15] = (Value *)fn_898;
incRef((Value *)fn_898);
incRef(reified_16);
decRef((Value *)fn_832);
my_free((Value *)fn_832);
decRef((Value *)fn_836);
my_free((Value *)fn_836);
decRef((Value *)fn_840);
my_free((Value *)fn_840);
decRef((Value *)fn_844);
my_free((Value *)fn_844);
decRef((Value *)fn_848);
my_free((Value *)fn_848);
decRef((Value *)fn_854);
my_free((Value *)fn_854);
decRef((Value *)fn_858);
my_free((Value *)fn_858);
decRef((Value *)fn_862);
my_free((Value *)fn_862);
decRef((Value *)fn_878);
my_free((Value *)fn_878);
decRef((Value *)fn_882);
my_free((Value *)fn_882);
decRef((Value *)fn_886);
my_free((Value *)fn_886);
decRef((Value *)fn_890);
my_free((Value *)fn_890);
decRef((Value *)fn_898);
my_free((Value *)fn_898);
decRef(reified_16);
my_free(reified_16);
return(reified_16);
};


// --------- invoke_impl main body --------------
Function fn_830 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_831}}};

Value *protoImpl_902(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_903 = {3, -1, "invoke", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_902}}};

ReifiedVal reified_904 = {18, -1, 2, {(Value *)&fn_826, (Value *)&fn_830}};
Value *var_825 = (Value *)&reified_904;

// --------- hash-map --------------
Function fn_905;
Value *arityImpl_906(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *)argsList;
Value *rslt0 = arityImpl_775(empty_list, arg0, (Value *)&_num_2);
Value *rslt4;
if((var_825)->type != 3) {
rslt4 = protoFnImpl_10(empty_list, var_825, rslt0);
} else {
FnArity *arity1 = findFnArity(var_825, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_825)->name);
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
Function fn_905 = {3, -1, "hash-map", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_906}}};

SubString _kw_6 = {5, -1, 10, 0, ":not-found"};

// --------- merge-with --------------
Function fn_908;

// --------- anon --------------
Function fn_910;

// --------- anon --------------
Function fn_912;
Value *arityImpl_913(List *closures, Value *arg0, Value *arg1) {
Value *val5 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *cond0;
Value *rslt13 = protoFnImpl_321(empty_list, arg1);
Value *rslt14 = arityImpl_429(empty_list, (Value *)&_num_2, rslt13);
Value *rslt15 = arityImpl_420(empty_list, rslt14);
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
Value *rslt1 = arityImpl_781(empty_list, arg1, (Value *)&_num_12);
Value *rslt2 = arityImpl_781(empty_list, arg1, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_402(empty_list, arg0, rslt1, (Value *)&_kw_6);
Value *cond4;
Value *rslt11 = arityImpl_429(empty_list, (Value *)&_kw_6, rslt3);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_396(empty_list, arg0, rslt1, rslt2);
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
Value *rslt10 = protoFnImpl_396(empty_list, arg0, rslt1, rslt9);
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

Value *arityImpl_911(List *closures, Value *arg0, Value *arg1) {
Value *val2 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
Value *rslt0 = protoFnImpl_345(empty_list, arg1);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = 8;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_913;
incRef((Value *)val2);
arity_1->closures = listCons((Value *)val2, (List *)arity_1->closures);
Function *fn_912 = malloc_function(1);
fn_912->type = 3;
fn_912->name = "anon";
fn_912->arityCount = 1;
fn_912->arities[0] = arity_1;
Value *rslt3 = protoFnImpl_331(empty_list, rslt0, arg0, (Value *)fn_912);
incRef(rslt3);
decRef(rslt0);
my_free(rslt0);
decRef((Value *)fn_912);
my_free((Value *)fn_912);
decRef(rslt3);
my_free(rslt3);
return(rslt3);
};

Value *arityImpl_909(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *)argsList;
Value *cond0;
Value *rslt3 = protoFnImpl_306(empty_list, arg2);
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
arity_1->fn = arityImpl_911;
incRef((Value *)arg0);
arity_1->closures = listCons((Value *)arg0, (List *)arity_1->closures);
Function *fn_910 = malloc_function(1);
fn_910->type = 3;
fn_910->name = "anon";
fn_910->arityCount = 1;
fn_910->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_331(empty_list, arg2, arg1, (Value *)fn_910);
incRef(rslt2);
cond0 = rslt2;
decRef((Value *)fn_910);
my_free((Value *)fn_910);
decRef(rslt2);
my_free(rslt2);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};

// --------- merge-with main body --------------
Function fn_908 = {3, -1, "merge-with", 1, {&(FnArity){8, -1, 2, (List *)0, 1, arityImpl_909}}};

SubString _kw_7 = {5, -1, 17, 0, ":get-in-not-found"};

// --------- get-in --------------
Function fn_915;
Value *arityImpl_916(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt7 = protoFnImpl_321(empty_list, arg1);
Value *rslt8 = arityImpl_429(empty_list, rslt7, (Value *)&_num_12);
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
Value *rslt9 = protoFnImpl_321(empty_list, arg1);
Value *rslt10 = arityImpl_429(empty_list, rslt9, (Value *)&_num_1);
decRef(rslt9);
my_free(rslt9);
decRef(rslt10);
my_free(rslt10);

if (isTrue(rslt10)) {
decRef(rslt10);
my_free(rslt10);
Value *rslt11 = protoFnImpl_350(empty_list, arg1);
Value *rslt12 = protoFnImpl_402(empty_list, arg0, rslt11, arg2);
incRef(rslt12);
cond0 = rslt12;
decRef(rslt11);
my_free(rslt11);
decRef(rslt12);
my_free(rslt12);
} else {
decRef(rslt10);
my_free(rslt10);
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_402(empty_list, arg0, rslt1, (Value *)&_kw_7);
Value *cond3;
Value *rslt6 = arityImpl_429(empty_list, (Value *)&_kw_7, rslt2);
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
Value *rslt4 = protoFnImpl_355(empty_list, arg1);
Value *rslt5 = arityImpl_916(closures, rslt2, rslt4, arg2);
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
Function fn_915 = {3, -1, "get-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_916}}};

SubString _kw_8 = {5, -1, 14, 0, ":update-in-nil"};

// --------- update-in --------------
Function fn_918;
Value *arityImpl_919(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt8 = protoFnImpl_321(empty_list, arg1);
Value *rslt9 = arityImpl_429(empty_list, rslt8, (Value *)&_num_12);
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
Value *rslt10 = protoFnImpl_321(empty_list, arg1);
Value *rslt11 = arityImpl_429(empty_list, rslt10, (Value *)&_num_1);
decRef(rslt10);
my_free(rslt10);
decRef(rslt11);
my_free(rslt11);

if (isTrue(rslt11)) {
decRef(rslt11);
my_free(rslt11);
Value *rslt12 = protoFnImpl_350(empty_list, arg1);
Value *rslt13 = protoFnImpl_402(empty_list, arg0, rslt12, (Value *)&_kw_8);
Value *cond14;
Value *rslt20 = arityImpl_429(empty_list, (Value *)&_kw_8, rslt13);
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
Value *rslt19 = protoFnImpl_396(empty_list, arg0, rslt12, rslt18);
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
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_402(empty_list, arg0, rslt1, (Value *)&_kw_8);
Value *cond3;
Value *rslt7 = arityImpl_429(empty_list, (Value *)&_kw_8, rslt2);
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
Value *rslt4 = protoFnImpl_355(empty_list, arg1);
Value *rslt5 = arityImpl_919(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_396(empty_list, arg0, rslt1, rslt5);
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
Function fn_918 = {3, -1, "update-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_919}}};

SubString _kw_9 = {5, -1, 13, 0, ":assoc-in-nil"};

// --------- assoc-in --------------
Function fn_921;
Value *arityImpl_922(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt13 = protoFnImpl_321(empty_list, arg1);
Value *rslt14 = arityImpl_429(empty_list, rslt13, (Value *)&_num_12);
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
Value *rslt15 = protoFnImpl_321(empty_list, arg1);
Value *rslt16 = arityImpl_429(empty_list, rslt15, (Value *)&_num_1);
decRef(rslt15);
my_free(rslt15);
decRef(rslt16);
my_free(rslt16);

if (isTrue(rslt16)) {
decRef(rslt16);
my_free(rslt16);
Value *rslt17 = protoFnImpl_350(empty_list, arg1);
Value *rslt18 = protoFnImpl_396(empty_list, arg0, rslt17, arg2);
incRef(rslt18);
cond0 = rslt18;
decRef(rslt17);
my_free(rslt17);
decRef(rslt18);
my_free(rslt18);
} else {
decRef(rslt16);
my_free(rslt16);
Value *rslt1 = protoFnImpl_350(empty_list, arg1);
Value *rslt2 = protoFnImpl_402(empty_list, arg0, rslt1, (Value *)&_kw_9);
Value *cond3;
Value *rslt7 = arityImpl_429(empty_list, (Value *)&_kw_9, rslt2);
decRef(rslt7);
my_free(rslt7);

if (isTrue(rslt7)) {
decRef(rslt7);
my_free(rslt7);
List *varArgs8 = empty_list;
Value *rslt9 = arityImpl_906(empty_list, (Value *)varArgs8);
decRef((Value *)varArgs8);
my_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_355(empty_list, arg1);
Value *rslt11 = arityImpl_922(closures, rslt9, rslt10, arg2);
Value *rslt12 = protoFnImpl_396(empty_list, arg0, rslt1, rslt11);
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
Value *rslt4 = protoFnImpl_355(empty_list, arg1);
Value *rslt5 = arityImpl_922(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_396(empty_list, arg0, rslt1, rslt5);
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
Function fn_921 = {3, -1, "assoc-in", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_922}}};


// --------- =*_impl --------------
Function fn_924;
Value *arityImpl_925(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt1 = arityImpl_91(empty_list, arg1);
Value *rslt2 = arityImpl_429(empty_list, rslt0, rslt1);
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
Function fn_924 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_925}}};

Value *protoImpl_926(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_927 = {3, -1, "=*", 1, {&(FnArity){8, -1, 2, (List *)0, 0, protoImpl_926}}};

ReifiedVal reified_928 = {20, -1, 1, {(Value *)&fn_924}};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[19];} _str_60 = {1, -1, 18,"Could not look up "};

// --------- =*_impl --------------
Function fn_930;
Value *arityImpl_931(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_148(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_930 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_931}}};


// --------- name_impl --------------
Function fn_932;
Value *arityImpl_933(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_76(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_932 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_933}}};


// --------- string-list_impl --------------
Function fn_934;
Value *arityImpl_935(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_258(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
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
Function fn_934 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_935}}};


// --------- invoke_impl --------------
Function fn_936;
Value *arityImpl_937(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_402(empty_list, arg1, arg0, (Value *)&reified_928);
Value *cond1;
Value *rslt2 = arityImpl_429(empty_list, (Value *)&reified_928, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_60);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_60, varArgs3);
Value *rslt4 = arityImpl_290(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_88(empty_list);
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
Function fn_936 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_937}}};


// --------- sha1_impl --------------
Function fn_938;
Value *arityImpl_939(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)&subStrVal->type, 8);
Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_938 = {3, -1, "sha1_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_939}}};


// --------- =*_impl --------------
Function fn_940;
Value *arityImpl_941(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_148(empty_list, arg0, arg1);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_940 = {3, -1, "=*_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_941}}};


// --------- name_impl --------------
Function fn_942;
Value *arityImpl_943(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_76(empty_list, arg0);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_942 = {3, -1, "name_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_943}}};


// --------- string-list_impl --------------
Function fn_944;
Value *arityImpl_945(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_258(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_244(empty_list, (Value *)varArgs1);
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
Function fn_944 = {3, -1, "string-list_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_945}}};


// --------- invoke_impl --------------
Function fn_946;
Value *arityImpl_947(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_402(empty_list, arg1, arg0, (Value *)&reified_928);
Value *cond1;
Value *rslt2 = arityImpl_429(empty_list, (Value *)&reified_928, rslt0);
decRef(rslt2);
my_free(rslt2);

if (isTrue(rslt2)) {
decRef(rslt2);
my_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_60);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_60, varArgs3);
Value *rslt4 = arityImpl_290(empty_list, (Value *)varArgs3);
decRef((Value *)varArgs3);
my_free((Value *)varArgs3);
Value *rslt5 = arityImpl_88(empty_list);
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
Function fn_946 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_947}}};


// --------- invoke_impl --------------
Function fn_948;
Value *arityImpl_949(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_402(empty_list, arg1, arg0, arg2);
incRef(rslt0);
decRef(rslt0);
my_free(rslt0);
return(rslt0);
};


// --------- invoke_impl main body --------------
Function fn_948 = {3, -1, "invoke_impl", 1, {&(FnArity){8, -1, 3, (List *)0, 0, arityImpl_949}}};


// --------- sha1_impl --------------
Function fn_950;
Value *arityImpl_951(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)&subStrVal->type, 8);
Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_950 = {3, -1, "sha1_impl", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_951}}};


// --------- symbol? --------------
Function fn_952;
Value *arityImpl_953(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_7, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- symbol? main body --------------
Function fn_952 = {3, -1, "symbol?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_953}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_61 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_955;
Value *arityImpl_956(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_61);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_61, varArgs0);
Value *rslt1 = arityImpl_752(empty_list, (Value *)varArgs0);
decRef((Value *)varArgs0);
my_free((Value *)varArgs0);
Value *rslt2 = arityImpl_85(empty_list, rslt1);
incRef(rslt2);
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
return(rslt2);
};


// --------- keyword main body --------------
Function fn_955 = {3, -1, "keyword", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_956}}};


// --------- keyword? --------------
Function fn_958;
Value *arityImpl_959(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_5, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- keyword? main body --------------
Function fn_958 = {3, -1, "keyword?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_959}}};


// --------- number? --------------
Function fn_961;
Value *arityImpl_962(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_2, rslt0);
incRef(rslt1);
decRef(rslt0);
my_free(rslt0);
decRef(rslt1);
my_free(rslt1);
return(rslt1);
};


// --------- number? main body --------------
Function fn_961 = {3, -1, "number?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_962}}};


// --------- string? --------------
Function fn_964;
Value *arityImpl_965(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_91(empty_list, arg0);
Value *rslt1 = arityImpl_429(empty_list, (Value *)&_num_1, rslt0);
Value *rslt2 = arityImpl_91(empty_list, arg0);
Value *rslt3 = arityImpl_429(empty_list, (Value *)&_num_6, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)rslt1);
varArgs4 = (List *)listCons((Value *)rslt1, varArgs4);
Value *rslt5 = arityImpl_426(empty_list, (Value *)varArgs4);
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
Function fn_964 = {3, -1, "string?", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_965}}};


// --------- range* --------------
Function fn_967;
Value *arityImpl_968(List *closures, Value *arg0) {
Value *cond0;
Value *rslt4 = arityImpl_429(empty_list, (Value *)&_num_12, arg0);
decRef(rslt4);
my_free(rslt4);

if (isTrue(rslt4)) {
decRef(rslt4);
my_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_num_12);
varArgs5 = (List *)listCons((Value *)(Value *)&_num_12, varArgs5);
Value *rslt6 = arityImpl_244(empty_list, (Value *)varArgs5);
decRef((Value *)varArgs5);
my_free((Value *)varArgs5);
incRef(rslt6);
cond0 = rslt6;
decRef(rslt6);
my_free(rslt6);
} else {
decRef(rslt4);
my_free(rslt4);
Value *rslt1 = arityImpl_580(empty_list, arg0);
Value *rslt2 = arityImpl_968(closures, rslt1);
Value *rslt3 = arityImpl_124(empty_list, arg0, rslt2);
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
Function fn_967 = {3, -1, "range*", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_968}}};


// --------- range --------------
Function fn_970;
Value *arityImpl_971(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_580(empty_list, arg0);
Value *rslt1 = arityImpl_968(empty_list, rslt0);
Value *rslt2 = arityImpl_451(empty_list, rslt1);
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
Function fn_970 = {3, -1, "range", 1, {&(FnArity){8, -1, 1, (List *)0, 0, arityImpl_971}}};


// --------- repeat --------------
Function fn_973;

// --------- anon --------------
Function fn_975;
Value *arityImpl_976(List *closures, Value *arg0) {
Value *val0 = closures->head;
if (closures->tail)
closures->tail->len = closures->len - 1;
closures = closures->tail;
incRef(val0);
return(val0);
};

Value *arityImpl_974(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_433(empty_list, arg0, (Value *)&_num_1);
decRef(rslt5);
my_free(rslt5);

if (isTrue(rslt5)) {
decRef(rslt5);
my_free(rslt5);
incRef(var_121);
cond0 = var_121;
} else {
decRef(rslt5);
my_free(rslt5);
Value *rslt1 = arityImpl_580(empty_list, arg0);
Value *rslt2 = arityImpl_968(empty_list, rslt1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = 8;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_976;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_975 = malloc_function(1);
fn_975->type = 3;
fn_975->name = "anon";
fn_975->arityCount = 1;
fn_975->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_252(empty_list, rslt2, (Value *)fn_975);
incRef(rslt4);
cond0 = rslt4;
decRef(rslt1);
my_free(rslt1);
decRef(rslt2);
my_free(rslt2);
decRef((Value *)fn_975);
my_free((Value *)fn_975);
decRef(rslt4);
my_free(rslt4);
}
incRef(cond0);
decRef(cond0);
my_free(cond0);
return(cond0);
};


// --------- repeat main body --------------
Function fn_973 = {3, -1, "repeat", 1, {&(FnArity){8, -1, 2, (List *)0, 0, arityImpl_974}}};

Value *assoc(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_391((List *)0, node, key, val, hash, shift));
}
Value *valsEqual(List *x, Value *v1, Value *v2) {
  return(protoFnImpl_295(x, v1, v2));
}
Value *sha1(Value *v) {
  return(protoFnImpl_417((List *)0, v));
}
Value *hashSeq(Value *n, Value *s) {
  return(protoFnImpl_386((List *)0, n, s));
}
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
numInfo = listCons(numberValue(10), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_11"), empty_list);
numInfo = listCons(numberValue(11), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_12"), empty_list);
numInfo = listCons(numberValue(0), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_13"), empty_list);
numInfo = listCons(numberValue(13), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_14"), empty_list);
numInfo = listCons(numberValue(16), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_15"), empty_list);
numInfo = listCons(numberValue(19), numInfo);
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
strInfo = listCons(stringValue("BitmapIndexedNode"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_10"), empty_list);
strInfo = listCons(stringValue("ArrayNode"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_11"), empty_list);
strInfo = listCons(stringValue("void"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_12"), empty_list);
strInfo = listCons(stringValue("char"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_13"), empty_list);
strInfo = listCons(stringValue("char *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_14"), empty_list);
strInfo = listCons(stringValue("int"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_15"), empty_list);
strInfo = listCons(stringValue("int64_t"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_16"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs;} Value;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_17"), empty_list);
strInfo = listCons(stringValue("Value *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_18"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_19"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_20"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; Value *source; char *buffer;} SubString;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_21"), empty_list);
strInfo = listCons(stringValue("typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_22"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_23"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_24"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_25"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_26"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_27"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_28"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int bitmap; Value *array[];} BitmapIndexedNode;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_29"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; Value *array[];} ArrayNode;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_30"), empty_list);
strInfo = listCons(stringValue(":match*-one-arg"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_31"), empty_list);
strInfo = listCons(stringValue(":match*-two-args"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_32"), empty_list);
strInfo = listCons(stringValue("*** call to 'instance?' with unknown type parameter."), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_33"), empty_list);
strInfo = listCons(stringValue("'flat-map' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_34"), empty_list);
strInfo = listCons(stringValue("'duplicate' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_35"), empty_list);
strInfo = listCons(stringValue("*** 'wrap' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_36"), empty_list);
strInfo = listCons(stringValue("'name' not implemented for type "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_37"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_38"), empty_list);
strInfo = listCons(stringValue("'serialize' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue(" "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_40"), empty_list);
strInfo = listCons(stringValue("\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_42"), empty_list);
strInfo = listCons(stringValue("'=*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_43"), empty_list);
strInfo = listCons(stringValue("'<*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_44"), empty_list);
strInfo = listCons(stringValue("'get' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_45"), empty_list);
strInfo = listCons(stringValue("<Fn: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_46"), empty_list);
strInfo = listCons(stringValue(">"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_47"), empty_list);
strInfo = listCons(stringValue("ZipList"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_48"), empty_list);
strInfo = listCons(stringValue("("), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_49"), empty_list);
strInfo = listCons(stringValue(", "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_50"), empty_list);
strInfo = listCons(stringValue(")"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_51"), empty_list);
strInfo = listCons(stringValue("<nothing>"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_52"), empty_list);
strInfo = listCons(stringValue("<maybe "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_53"), empty_list);
strInfo = listCons(stringValue("maybe-val"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_54"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_55"), empty_list);
strInfo = listCons(stringValue("'nth' from empty seq"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_56"), empty_list);
strInfo = listCons(stringValue("{}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_57"), empty_list);
strInfo = listCons(stringValue("{"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_58"), empty_list);
strInfo = listCons(stringValue("}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_59"), empty_list);
strInfo = listCons(stringValue("HashMap"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_60"), empty_list);
strInfo = listCons(stringValue("Could not look up "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_61"), empty_list);
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
impl = listCons(stringValue("(Value *)&fn_42"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_44"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_498"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_669"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_897"), impl);
impl = listCons(numberValue(19), impl);
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
impl = listCons(stringValue("(Value *)&protoFn_504"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_675"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_680"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_903"), impl);
impl = listCons(numberValue(18), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_936"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_948"), impl);
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
protoInfo = listCons(stringValue("extern Function protoFn_172;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_171"), protoInfo);
protoInfo = listCons(stringValue("core/Variant/bippity"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_178"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("match*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_177;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_176"), protoInfo);
protoInfo = listCons(stringValue("core/Variant/match*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_186"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_486"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_627"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_684"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_829"), impl);
impl = listCons(numberValue(18), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("instance?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_185;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_184"), protoInfo);
protoInfo = listCons(stringValue("core/Type/instance?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_192"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_565"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_621"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_665"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flat-map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_191;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_190"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flat-map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_198"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_617"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_661"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flatten"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_197;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_196"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flatten"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extract"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_205;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_204"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extract"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extend"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_210;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_209"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extend"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_216"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("duplicate"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_215;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_214"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/duplicate"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_223"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_563"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_609"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_653"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("wrap"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_222;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_221"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/wrap"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_229"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_466"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_494"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_613"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_657"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("apply*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_228;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_227"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_248"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_561"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_605"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_649"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_247;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_246"), protoInfo);
protoInfo = listCons(stringValue("core/Functor/map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_256"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_932"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_942"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_255;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_254"), protoInfo);
protoInfo = listCons(stringValue("core/Named/name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_262"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_456"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_472"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_537"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_589"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_633"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_713"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_723"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_804"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_853"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_934"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_944"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("string-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_261;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_260"), protoInfo);
protoInfo = listCons(stringValue("core/Stringable/string-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_268"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("serialize"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_267;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_266"), protoInfo);
protoInfo = listCons(stringValue("core/Serializable/serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_293"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_468"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_535"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_593"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_637"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_695"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_725"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_847"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_927"), impl);
impl = listCons(numberValue(20), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_930"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_940"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("=*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_292;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_291"), protoInfo);
protoInfo = listCons(stringValue("core/Eq/=*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_299"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_470"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("<*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_298;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_297"), protoInfo);
protoInfo = listCons(stringValue("core/Ord/<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_539"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_697"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_727"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_800"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_857"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_304;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_303"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_541"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_699"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_729"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_309;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_308"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("destruct"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_314;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_313"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/destruct"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_545"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_701"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_731"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_861"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("count"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_319;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_318"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/count"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_543"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_703"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_733"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("conj"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_324;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_323"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/conj"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_547"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_705"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_735"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_865"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("reduce"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_329;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_328"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/reduce"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_338"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_549"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_337;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_336"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_551"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_707"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_737"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_802"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_835"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_343;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_342"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_553"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_709"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_739"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_839"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_348;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_347"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_555"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_711"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_741"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_843"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("rest"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_353;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_352"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_533"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("traverse"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_361;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_360"), protoInfo);
protoInfo = listCons(stringValue("core/Traversable/traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_529"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("crush"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_366;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_365"), protoInfo);
protoInfo = listCons(stringValue("core/Crushable/crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_458"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_557"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_597"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_641"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_688"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_869"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("zero"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_371;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_370"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_460"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_559"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_601"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_645"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_692"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_715"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_743"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_877"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("comp*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_376;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_375"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/comp*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_808"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("hash-seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_384;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_383"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/hash-seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_810"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_389;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_388"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/assoc*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_818"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_881"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_394;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_393"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_400"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_812"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_885"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_399;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_398"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_814"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_889"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("keys"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_405;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_404"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_816"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_893"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("vals"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_410;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_409"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_721"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_749"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_938"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_950"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("sha1"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_415;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_414"), protoInfo);
protoInfo = listCons(stringValue("core/Hash/sha1"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_502"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_673"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".v"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_478;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_477"), protoInfo);
protoInfo = listCons(stringValue("Getter/.v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_901"), impl);
impl = listCons(numberValue(19), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".a-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_821;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_820"), protoInfo);
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
arityInfo = listCons(stringValue("arityImpl_43"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_42"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_45"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_44"), fnInfo);
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
arityInfo = listCons(numberValue(0), arityInfo);
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
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_87"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_91"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_90"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_94"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_93"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_97"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_98"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_96"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_123"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_124"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_122"), fnInfo);
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
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_138"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_142"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_141"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_145"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_153"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_157"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_162"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_166"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_165"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_169"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_168"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_174"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_172"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_180"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("protoFnImpl_182"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_177"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_188"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_201"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_200"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_202"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_197"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_207"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_205"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_212"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_210"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_218"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_215"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_225"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_222"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_235"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_228"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_238"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_237"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_241"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_240"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_244"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_243"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_252"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_247"), fnInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_270"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_267"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_273"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_272"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_276"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_275"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_287"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_286"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_290"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_289"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_295"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_292"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_301"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_298"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_306"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_304"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_311"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_309"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_316"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_314"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_321"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_319"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_326"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_324"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_331"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_329"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_334"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_333"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_340"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_337"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_345"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_343"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_350"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_348"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_355"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_353"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_358"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_357"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_363"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_373"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_371"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_378"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_376"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_381"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_380"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_386"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_384"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_391"), empty_list);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_389"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_396"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_394"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_402"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_399"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_407"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_405"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_412"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_410"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_417"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_415"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_420"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_419"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_423"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_422"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_426"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_425"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_429"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_430"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_428"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_433"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_434"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_432"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_437"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_436"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_440"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_439"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_443"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_442"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_446"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_445"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_451"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_450"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_454"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_453"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_457"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_456"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_459"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_458"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_467"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_466"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_469"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_468"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_471"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_470"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_473"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_472"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_475"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_474"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_480"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_478"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_484"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_483"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_492"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_491"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_496"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_495"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_488"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_487"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_507"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_506"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_516"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_515"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_512"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_511"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_522"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_521"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_527"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_526"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_525"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_524"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_530"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_529"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_534"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_537"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_540"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_547"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_550"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_549"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_552"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_551"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_554"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_553"), fnInfo);
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
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_557"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_560"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_559"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_562"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_561"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_564"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_567"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_571"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_570"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_574"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_573"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_577"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_576"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_580"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_579"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_583"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_582"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_587"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_586"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_591"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_590"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_595"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_594"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_599"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_598"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_603"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_602"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_607"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_606"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_611"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_610"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_625"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_624"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_631"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_630"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_639"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_638"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_643"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_642"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_651"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_650"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_655"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_654"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_667"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_666"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_629"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_628"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_678"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_677"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_682"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_681"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_686"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_685"), fnInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_695"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_698"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_703"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_706"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_714"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_713"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_718"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_717"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_716"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_715"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_722"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_721"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_724"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_723"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_726"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_725"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_728"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_727"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_730"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_733"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_736"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_735"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_738"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_746"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_745"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_744"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_743"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_750"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_749"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_754"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_753"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_752"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_751"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_759"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_758"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_762"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_761"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_765"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_766"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_764"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_769"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_768"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_772"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_771"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_775"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_774"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_778"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_777"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_781"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(stringValue("arityImpl_782"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_780"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_785"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_784"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_788"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_787"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_791"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_790"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_794"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_793"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_797"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_796"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_801"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_800"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_803"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_802"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_807"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_806"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_805"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_804"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_809"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_808"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_811"), empty_list);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_810"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_813"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_812"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_815"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_814"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_817"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_816"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_819"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_818"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("protoFnImpl_823"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_821"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_827"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_826"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_851"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_850"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_867"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_866"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_875"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_874"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_873"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_872"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_871"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_870"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_895"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_894"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_831"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_830"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_906"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_905"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_909"), empty_list);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_908"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_916"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_915"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_919"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_918"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_922"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_921"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_925"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_924"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_931"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_930"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_933"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_932"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_935"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_934"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_937"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_936"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_939"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_938"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_941"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_940"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_943"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_942"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_945"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_944"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_947"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_946"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_949"), empty_list);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_948"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_951"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_950"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_953"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_952"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_956"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_955"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_959"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_958"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_962"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_961"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_965"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_964"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_968"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_967"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_971"), empty_list);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_970"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(stringValue("arityImpl_974"), empty_list);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_973"), fnInfo);
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
symInfo = listCons(stringValue("(Value *)&_num_10"), empty_list);
symInfo = listCons(stringValue("Number _num_10"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("BitmapIndexedNode"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_num_11"), empty_list);
symInfo = listCons(stringValue("Number _num_11"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ArrayNode"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_894"), empty_list);
symInfo = listCons(stringValue("Function fn_894"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_289"), empty_list);
symInfo = listCons(stringValue("Function fn_289"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print-err"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_11"), empty_list);
symInfo = listCons(stringValue("String _str_11"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("VoidT"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_12"), empty_list);
symInfo = listCons(stringValue("String _str_12"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_13"), empty_list);
symInfo = listCons(stringValue("String _str_13"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_14"), empty_list);
symInfo = listCons(stringValue("String _str_14"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int32"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_15"), empty_list);
symInfo = listCons(stringValue("String _str_15"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int64"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_15"), empty_list);
symInfo = listCons(stringValue(""), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ValueType"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_16"), empty_list);
symInfo = listCons(stringValue("String _str_16"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_17"), empty_list);
symInfo = listCons(stringValue("String _str_17"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_18"), empty_list);
symInfo = listCons(stringValue("String _str_18"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("NumberVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_19"), empty_list);
symInfo = listCons(stringValue("String _str_19"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("StringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_20"), empty_list);
symInfo = listCons(stringValue("String _str_20"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("SubStringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_21"), empty_list);
symInfo = listCons(stringValue("String _str_21"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ListVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_22"), empty_list);
symInfo = listCons(stringValue("String _str_22"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArityVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_23"), empty_list);
symInfo = listCons(stringValue("String _str_23"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FunctionVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_24"), empty_list);
symInfo = listCons(stringValue("String _str_24"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_25"), empty_list);
symInfo = listCons(stringValue("String _str_25"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpls"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_26"), empty_list);
symInfo = listCons(stringValue("String _str_26"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ReifiedVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_27"), empty_list);
symInfo = listCons(stringValue("String _str_27"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("OpaqueVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_28"), empty_list);
symInfo = listCons(stringValue("String _str_28"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("BitmapIndexedVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&_str_29"), empty_list);
symInfo = listCons(stringValue("String _str_29"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ArrayNodeVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_67"), empty_list);
symInfo = listCons(stringValue("Value *var_67;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("true"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_68"), empty_list);
symInfo = listCons(stringValue("Value *var_68;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("false"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_69"), empty_list);
symInfo = listCons(stringValue("Function fn_69"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("output-to-file"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_72"), empty_list);
symInfo = listCons(stringValue("Function fn_72"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("standard-output"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_75"), empty_list);
symInfo = listCons(stringValue("Function fn_75"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_78"), empty_list);
symInfo = listCons(stringValue("Function fn_78"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char-code"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_81"), empty_list);
symInfo = listCons(stringValue("Function fn_81"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_84"), empty_list);
symInfo = listCons(stringValue("Function fn_84"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("new-keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_87"), empty_list);
symInfo = listCons(stringValue("Function fn_87"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("abort"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_90"), empty_list);
symInfo = listCons(stringValue("Function fn_90"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-type"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_93"), empty_list);
symInfo = listCons(stringValue("Function fn_93"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_96"), empty_list);
symInfo = listCons(stringValue("Function fn_96"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subs"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_100"), empty_list);
symInfo = listCons(stringValue("Function fn_100"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_103"), empty_list);
symInfo = listCons(stringValue("Function fn_103"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_106"), empty_list);
symInfo = listCons(stringValue("Function fn_106"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-less-than"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_109"), empty_list);
symInfo = listCons(stringValue("Function fn_109"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("add-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_112"), empty_list);
symInfo = listCons(stringValue("Function fn_112"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subtract-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_115"), empty_list);
symInfo = listCons(stringValue("Function fn_115"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("mult-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_118"), empty_list);
symInfo = listCons(stringValue("Function fn_118"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rem"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_121"), empty_list);
symInfo = listCons(stringValue("Value *var_121;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_122"), empty_list);
symInfo = listCons(stringValue("Function fn_122"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cons"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_126"), empty_list);
symInfo = listCons(stringValue("Function fn_126"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_129"), empty_list);
symInfo = listCons(stringValue("Function fn_129"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("car"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_132"), empty_list);
symInfo = listCons(stringValue("Function fn_132"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cdr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_135"), empty_list);
symInfo = listCons(stringValue("Function fn_135"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_138"), empty_list);
symInfo = listCons(stringValue("Function fn_138"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_141"), empty_list);
symInfo = listCons(stringValue("Function fn_141"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_144"), empty_list);
symInfo = listCons(stringValue("Function fn_144"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_147"), empty_list);
symInfo = listCons(stringValue("Function fn_147"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_150"), empty_list);
symInfo = listCons(stringValue("Function fn_150"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-malloc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_153"), empty_list);
symInfo = listCons(stringValue("Function fn_153"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-append"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_156"), empty_list);
symInfo = listCons(stringValue("Function fn_156"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr-err*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_159"), empty_list);
symInfo = listCons(stringValue("Function fn_159"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("slurp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_162"), empty_list);
symInfo = listCons(stringValue("Function fn_162"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_165"), empty_list);
symInfo = listCons(stringValue("Function fn_165"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("escape-chars"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_168"), empty_list);
symInfo = listCons(stringValue("Function fn_168"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_172"), empty_list);
symInfo = listCons(stringValue("Function protoFn_172"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("bippity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_177"), empty_list);
symInfo = listCons(stringValue("Function protoFn_177"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("match*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_185"), empty_list);
symInfo = listCons(stringValue("Function protoFn_185"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_191"), empty_list);
symInfo = listCons(stringValue("Function protoFn_191"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_975"), empty_list);
symInfo = listCons(stringValue("Function fn_975"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_197"), empty_list);
symInfo = listCons(stringValue("Function protoFn_197"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_205"), empty_list);
symInfo = listCons(stringValue("Function protoFn_205"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extract"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_210"), empty_list);
symInfo = listCons(stringValue("Function protoFn_210"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_215"), empty_list);
symInfo = listCons(stringValue("Function protoFn_215"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("duplicate"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_511"), empty_list);
symInfo = listCons(stringValue("Function fn_511"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comprehend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_222"), empty_list);
symInfo = listCons(stringValue("Function protoFn_222"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_228"), empty_list);
symInfo = listCons(stringValue("Function protoFn_228"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_237"), empty_list);
symInfo = listCons(stringValue("Function fn_237"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_240"), empty_list);
symInfo = listCons(stringValue("Function fn_240"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply-to"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_243"), empty_list);
symInfo = listCons(stringValue("Function fn_243"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_247"), empty_list);
symInfo = listCons(stringValue("Function protoFn_247"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_255"), empty_list);
symInfo = listCons(stringValue("Function protoFn_255"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_261"), empty_list);
symInfo = listCons(stringValue("Function protoFn_261"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_267"), empty_list);
symInfo = listCons(stringValue("Function protoFn_267"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_272"), empty_list);
symInfo = listCons(stringValue("Function fn_272"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_275"), empty_list);
symInfo = listCons(stringValue("Function fn_275"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_280"), empty_list);
symInfo = listCons(stringValue("Function fn_280"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("prn"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_283"), empty_list);
symInfo = listCons(stringValue("Function fn_283"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_286"), empty_list);
symInfo = listCons(stringValue("Function fn_286"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_292"), empty_list);
symInfo = listCons(stringValue("Function protoFn_292"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_298"), empty_list);
symInfo = listCons(stringValue("Function protoFn_298"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_304"), empty_list);
symInfo = listCons(stringValue("Function protoFn_304"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_309"), empty_list);
symInfo = listCons(stringValue("Function protoFn_309"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_314"), empty_list);
symInfo = listCons(stringValue("Function protoFn_314"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("destruct"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_319"), empty_list);
symInfo = listCons(stringValue("Function protoFn_319"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_324"), empty_list);
symInfo = listCons(stringValue("Function protoFn_324"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_329"), empty_list);
symInfo = listCons(stringValue("Function protoFn_329"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_333"), empty_list);
symInfo = listCons(stringValue("Function fn_333"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_337"), empty_list);
symInfo = listCons(stringValue("Function protoFn_337"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_343"), empty_list);
symInfo = listCons(stringValue("Function protoFn_343"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_348"), empty_list);
symInfo = listCons(stringValue("Function protoFn_348"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_353"), empty_list);
symInfo = listCons(stringValue("Function protoFn_353"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_357"), empty_list);
symInfo = listCons(stringValue("Function fn_357"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("second"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_361"), empty_list);
symInfo = listCons(stringValue("Function protoFn_361"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_366"), empty_list);
symInfo = listCons(stringValue("Function protoFn_366"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_371"), empty_list);
symInfo = listCons(stringValue("Function protoFn_371"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_376"), empty_list);
symInfo = listCons(stringValue("Function protoFn_376"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_380"), empty_list);
symInfo = listCons(stringValue("Function fn_380"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_384"), empty_list);
symInfo = listCons(stringValue("Function protoFn_384"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_389"), empty_list);
symInfo = listCons(stringValue("Function protoFn_389"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_394"), empty_list);
symInfo = listCons(stringValue("Function protoFn_394"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_399"), empty_list);
symInfo = listCons(stringValue("Function protoFn_399"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_405"), empty_list);
symInfo = listCons(stringValue("Function protoFn_405"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_410"), empty_list);
symInfo = listCons(stringValue("Function protoFn_410"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_415"), empty_list);
symInfo = listCons(stringValue("Function protoFn_415"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("sha1"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_419"), empty_list);
symInfo = listCons(stringValue("Function fn_419"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_422"), empty_list);
symInfo = listCons(stringValue("Function fn_422"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("and"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_425"), empty_list);
symInfo = listCons(stringValue("Function fn_425"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("or"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_428"), empty_list);
symInfo = listCons(stringValue("Function fn_428"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_432"), empty_list);
symInfo = listCons(stringValue("Function fn_432"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_436"), empty_list);
symInfo = listCons(stringValue("Function fn_436"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_439"), empty_list);
symInfo = listCons(stringValue("Function fn_439"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_442"), empty_list);
symInfo = listCons(stringValue("Function fn_442"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("filter"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_445"), empty_list);
symInfo = listCons(stringValue("Function fn_445"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_450"), empty_list);
symInfo = listCons(stringValue("Function fn_450"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_453"), empty_list);
symInfo = listCons(stringValue("Function fn_453"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_944"), empty_list);
symInfo = listCons(stringValue("Function fn_944"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_866"), empty_list);
symInfo = listCons(stringValue("Function fn_866"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_870"), empty_list);
symInfo = listCons(stringValue("Function fn_870"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_654"), empty_list);
symInfo = listCons(stringValue("Function fn_654"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_940"), empty_list);
symInfo = listCons(stringValue("Function fn_940"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_470"), empty_list);
symInfo = listCons(stringValue("Function fn_470"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_474"), empty_list);
symInfo = listCons(stringValue("Function fn_474"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("any?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_478"), empty_list);
symInfo = listCons(stringValue("Function protoFn_478"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_482"), empty_list);
symInfo = listCons(stringValue("Value *var_482"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ZipList"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_826"), empty_list);
symInfo = listCons(stringValue("Function fn_826"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_948"), empty_list);
symInfo = listCons(stringValue("Function fn_948"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_670"), empty_list);
symInfo = listCons(stringValue("Function fn_670"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_506"), empty_list);
symInfo = listCons(stringValue("Function fn_506"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partial"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_521"), empty_list);
symInfo = listCons(stringValue("Function fn_521"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-concat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_524"), empty_list);
symInfo = listCons(stringValue("Function fn_524"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_529"), empty_list);
symInfo = listCons(stringValue("Function fn_529"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_533"), empty_list);
symInfo = listCons(stringValue("Function fn_533"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_854"), empty_list);
symInfo = listCons(stringValue("Function fn_854"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_729"), empty_list);
symInfo = listCons(stringValue("Function fn_729"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_733"), empty_list);
symInfo = listCons(stringValue("Function fn_733"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_858"), empty_list);
symInfo = listCons(stringValue("Function fn_858"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_862"), empty_list);
symInfo = listCons(stringValue("Function fn_862"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_549"), empty_list);
symInfo = listCons(stringValue("Function fn_549"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_832"), empty_list);
symInfo = listCons(stringValue("Function fn_832"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_836"), empty_list);
symInfo = listCons(stringValue("Function fn_836"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_840"), empty_list);
symInfo = listCons(stringValue("Function fn_840"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_646"), empty_list);
symInfo = listCons(stringValue("Function fn_646"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_650"), empty_list);
symInfo = listCons(stringValue("Function fn_650"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_662"), empty_list);
symInfo = listCons(stringValue("Function fn_662"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_567"), empty_list);
symInfo = listCons(stringValue("Function fn_567"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("some"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_570"), empty_list);
symInfo = listCons(stringValue("Function fn_570"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("inc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_573"), empty_list);
symInfo = listCons(stringValue("Function fn_573"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_576"), empty_list);
symInfo = listCons(stringValue("Function fn_576"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_579"), empty_list);
symInfo = listCons(stringValue("Function fn_579"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_582"), empty_list);
symInfo = listCons(stringValue("Function fn_582"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("-"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_585"), empty_list);
symInfo = listCons(stringValue("Value *var_585"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe-val"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_658"), empty_list);
symInfo = listCons(stringValue("Function fn_658"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_622"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_622"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nothing"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_693"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_693"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_950"), empty_list);
symInfo = listCons(stringValue("Function fn_950"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("sha1_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_751"), empty_list);
symInfo = listCons(stringValue("Function fn_751"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_758"), empty_list);
symInfo = listCons(stringValue("Function fn_758"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_761"), empty_list);
symInfo = listCons(stringValue("Function fn_761"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("drop"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_764"), empty_list);
symInfo = listCons(stringValue("Function fn_764"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_768"), empty_list);
symInfo = listCons(stringValue("Function fn_768"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("replace-at-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_771"), empty_list);
symInfo = listCons(stringValue("Function fn_771"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_774"), empty_list);
symInfo = listCons(stringValue("Function fn_774"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_777"), empty_list);
symInfo = listCons(stringValue("Function fn_777"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition-all"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_780"), empty_list);
symInfo = listCons(stringValue("Function fn_780"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_784"), empty_list);
symInfo = listCons(stringValue("Function fn_784"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("last"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_787"), empty_list);
symInfo = listCons(stringValue("Function fn_787"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_790"), empty_list);
symInfo = listCons(stringValue("Function fn_790"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_793"), empty_list);
symInfo = listCons(stringValue("Function fn_793"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map-get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_796"), empty_list);
symInfo = listCons(stringValue("Function fn_796"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_799"), empty_list);
symInfo = listCons(stringValue("Value *var_799;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("emptyBMI"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_808"), empty_list);
symInfo = listCons(stringValue("Function fn_808"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_810"), empty_list);
symInfo = listCons(stringValue("Function fn_810"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_882"), empty_list);
symInfo = listCons(stringValue("Function fn_882"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_886"), empty_list);
symInfo = listCons(stringValue("Function fn_886"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_890"), empty_list);
symInfo = listCons(stringValue("Function fn_890"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_878"), empty_list);
symInfo = listCons(stringValue("Function fn_878"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&protoFn_821"), empty_list);
symInfo = listCons(stringValue("Function protoFn_821"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("var_825"), empty_list);
symInfo = listCons(stringValue("Value *var_825"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("HashMap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_898"), empty_list);
symInfo = listCons(stringValue("Function fn_898"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".a-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_905"), empty_list);
symInfo = listCons(stringValue("Function fn_905"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_908"), empty_list);
symInfo = listCons(stringValue("Function fn_908"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_915"), empty_list);
symInfo = listCons(stringValue("Function fn_915"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_918"), empty_list);
symInfo = listCons(stringValue("Function fn_918"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_921"), empty_list);
symInfo = listCons(stringValue("Function fn_921"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&reified_928"), empty_list);
symInfo = listCons(stringValue("ReifiedVal reified_928"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-found"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_942"), empty_list);
symInfo = listCons(stringValue("Function fn_942"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_952"), empty_list);
symInfo = listCons(stringValue("Function fn_952"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_955"), empty_list);
symInfo = listCons(stringValue("Function fn_955"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_958"), empty_list);
symInfo = listCons(stringValue("Function fn_958"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_961"), empty_list);
symInfo = listCons(stringValue("Function fn_961"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_964"), empty_list);
symInfo = listCons(stringValue("Function fn_964"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_967"), empty_list);
symInfo = listCons(stringValue("Function fn_967"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_970"), empty_list);
symInfo = listCons(stringValue("Function fn_970"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(stringValue("(Value *)&fn_973"), empty_list);
symInfo = listCons(stringValue("Function fn_973"), symInfo);
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
typeInfo = listCons(symbolValue("BitmapIndexedNode"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(11), empty_list);
typeInfo = listCons(symbolValue("ArrayNode"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(12), empty_list);
typeInfo = listCons(symbolValue("12"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(13), empty_list);
typeInfo = listCons(symbolValue("ZipList"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(14), empty_list);
typeInfo = listCons(symbolValue("14"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(15), empty_list);
typeInfo = listCons(symbolValue("15"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(16), empty_list);
typeInfo = listCons(symbolValue("maybe-val"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(17), empty_list);
typeInfo = listCons(symbolValue("17"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(18), empty_list);
typeInfo = listCons(symbolValue("18"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(19), empty_list);
typeInfo = listCons(symbolValue("HashMap"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(20), empty_list);
typeInfo = listCons(symbolValue("20"), typeInfo);
types = listCons((Value *)typeInfo, types);
return((Value *)types);
}


Value *counts() {
List *cnts = empty_list;
cnts = listCons(numberValue(978), cnts);
return((Value *)cnts);
}

