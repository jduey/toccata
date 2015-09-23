#include <sys/types.h>
#include <stdio.h>
#include <string.h>

typedef struct {int64_t type; int32_t refs;} Value;
typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;
typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;
typedef struct {int64_t type; int32_t refs; int64_t len; Number *hash; Value *source; char *buffer;} SubString;
typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;
typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;
typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;
typedef struct {int64_t type; Value *implFn;} ProtoImpl;
typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;
typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;
typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;
typedef struct {int64_t type; int32_t refs; int32_t bitmap; Value *array[];} BitmapIndexedNode;
typedef struct {int64_t type; int32_t refs; Value *array[32];} ArrayNode;
typedef struct {int64_t type; int32_t refs; int16_t count; Value *array[];} HashCollisionNode;
List *listCons(Value *x, List *l);
Value *stringValue(char *s);
#define NumberType 2
#define KeywordType 5
#define SymbolType 7
#define StringType 1
#define SubStringType 6
#define ListType 4
#define FunctionType 3
#define FnArityType 8
#define OpaqueType 9
#define BitmapIndexedType 10
#define ArrayNodeType 11
#define HashCollisionNodeType 12
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
List *empty_list = &(List){4,-1,0,0,0};

FILE *outStream;
Number trueVal = {NumberType, -1, 1};
Value* true = (Value *)&trueVal;
Number falseVal = {NumberType, -1, 0};
Value* false = (Value *)&falseVal;
long long malloc_count = 0;
long long free_count = 0;

int mask(int64_t hash, int shift) {
  return (hash >> shift) & 0x1f;
}

int bitpos(int64_t hash, int shift) {
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
    ((SubString *)subStr)->hash = (Number *)0;
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

DirectLL *freeBMINodes[20] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
BitmapIndexedNode *malloc_bmiNode(int itemCount) {
  int nodeSize = sizeof(BitmapIndexedNode) + sizeof(Value *) * (itemCount * 2);
  BitmapIndexedNode *bmiNode;
  if (freeBMINodes[itemCount] == (DirectLL *)0) {
    malloc_count--;
    bmiNode = (BitmapIndexedNode *)my_malloc(nodeSize);
  } else {
    bmiNode = (BitmapIndexedNode *)freeBMINodes[itemCount];
    freeBMINodes[itemCount] = ((DirectLL *)bmiNode)->next;
  }
  memset(bmiNode, 0, nodeSize);
  bmiNode->type = BitmapIndexedType;
  bmiNode->refs = 1;
  return(bmiNode);
}

HashCollisionNode *malloc_hashCollisionNode(int itemCount) {
  if (itemCount > 30000) {
     fprintf(stderr, "Catastrophic failure: Too many hash collisions\n");     abort();
  }
  int nodeSize = sizeof(HashCollisionNode) + sizeof(Value *) * (itemCount * 2);
  HashCollisionNode *collisionNode;
  collisionNode = (HashCollisionNode *)my_malloc(nodeSize);
  memset(collisionNode, 0, nodeSize);
  collisionNode->type = HashCollisionNodeType;
  collisionNode->count = itemCount * 2;
  collisionNode->refs = 1;
  return(collisionNode);
}

DirectLL *freeArrayNodes = (DirectLL *)0;
ArrayNode *malloc_arrayNode() {
  ArrayNode *arrayNode;
  if (freeArrayNodes == (DirectLL *)0) {
    malloc_count--;
    arrayNode = (ArrayNode *)my_malloc(sizeof(ArrayNode));
  } else {
    arrayNode = (ArrayNode *)freeArrayNodes;
    freeArrayNodes = ((DirectLL *)arrayNode)->next;
  }
  memset(arrayNode, 0, sizeof(ArrayNode));
  arrayNode->type = ArrayNodeType;
  arrayNode->refs = 1;
  return(arrayNode);}

void dec_and_free(Value *v) {
  if (v == (Value *)0) {
    fprintf(stderr, "why are you freeing 'null'\n");
     abort();
  } else if (v->refs == -10) {
    fprintf(stderr, "freeing already freed struct\n");
    abort();
  } else if (v->refs == -1) {
    return;
  } else if (v->refs > 1) {
    v->refs--;
    return;
  } else if (v->type == 0) {
    fprintf(stderr, "freeing invalid type\n");
    abort();
  } else if (v->type == StringType) {
    v->refs = -10;
    free_count++;
    free(v);
  } else if (v->type == NumberType) {
    v->refs = -10;
    ((DirectLL *)v)->next = freeNumbers;
    freeNumbers = (DirectLL *)v;
  } else if (v->type == FunctionType) {
    Function *f = (Function *)v;
    for (int i = 0; i < f->arityCount; i++) {
      dec_and_free((Value *)f->arities[i]);
    }
    v->refs = -10;
    if (f->arityCount < 10) {
      DirectLL *freedList = freeFunctions[f->arityCount];
      freeFunctions[f->arityCount] = (DirectLL *)v;
      ((DirectLL *)v)->next = freedList;
    } else {
      free_count++;
      free(v);
    }  } else if (v->type == ListType) {
    Value *head = ((List *)v)->head;
    List *tail = ((List *)v)->tail;
    v->refs = -10;
    if (head != (Value *)0) {
      dec_and_free(head);
    }
    if (tail != (List *)0) {
      dec_and_free((Value *)tail);
    }
    ((DirectLL *)v)->next = freeLists;
    freeLists = (DirectLL *)v;
  } else if (v->type == KeywordType ||
             v->type == SubStringType ||
             v->type == SymbolType) {
    Value *src = ((SubString *)v)->source;
    Number *hash = ((SubString *)v)->hash;
    v->refs = -10;
    if (src != (Value *)0) {
      dec_and_free(src);
    }
    if (v->type == KeywordType && hash != (Number *)0) {
      dec_and_free((Value *)hash);
    }
    ((DirectLL *)v)->next = freeSubStrings;
    freeSubStrings = (DirectLL *)v;
  } else if (v->type == FnArityType) {
    FnArity *arity = (FnArity *)v;
    dec_and_free((Value *)arity->closures);
    v->refs = -10;
    ((DirectLL *)v)->next = freeFnAritys;
    freeFnAritys = (DirectLL *)v;
  } else if (v->type == OpaqueType) {
    v->refs = -10;
  } else if (v->type == BitmapIndexedType) {
    // fprintf(stderr, "%p free bmi node\n", v);
    BitmapIndexedNode *node = (BitmapIndexedNode *)v;
    int cnt = __builtin_popcount(node->bitmap);
    for (int i = 0; i < (2 * cnt); i++) {
       if (node->array[i] != (Value *)0) {
          dec_and_free(node->array[i]);
       }
    }
    v->refs = -10;
    ((DirectLL *)v)->next = freeBMINodes[cnt];
    freeBMINodes[cnt] = (DirectLL *)v;
  } else if (v->type == ArrayNodeType) {
    ArrayNode *node = (ArrayNode *)v;
    for (int i = 0; i < 32; i++) {
       if (node->array[i] != (Value *)0) {
          dec_and_free(node->array[i]);
       }
    }
    v->refs = -10;
    ((DirectLL *)v)->next = freeArrayNodes;
    freeArrayNodes = (DirectLL *)v;
  } else if (v->type == HashCollisionNodeType) {
    HashCollisionNode *node = (HashCollisionNode *)v;
    for (int i = 0; i < node->count; i++) {
       if (node->array[i] != (Value *)0) {
          dec_and_free(node->array[i]);
       }
    }
    v->refs = -10;
    free_count++;
    free(v);
  } else {
    ReifiedVal *rv = (ReifiedVal *)v;
    for (int i = 0; i < rv->implCount; i++) {
      dec_and_free(rv->impls[i]);
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

int64_t isTrue(Value *boolVal) {
if (boolVal->type != NumberType) {
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

FnArity *findFnArity(Value *fnVal, int64_t argCount) {
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
sym->len = strlen(s);
sym->source = (Value *)0;
sym->hash = (Number *)0;
return((Value *)sym);
};

Value *keywordValue(char *s) {
SubString *kw = malloc_substring();
kw->type = KeywordType;
kw->buffer = s;
kw->hash = (Number *)0;
kw->len = strlen(s);
kw->source = (Value *)0;
return((Value *)kw);
};

Value *makeSubstr(int64_t len, Value *str, char *subsStart) {
SubString *subStr = malloc_substring();
subStr->type = SubStringType;
subStr->len = len;
subStr->source = str;
subStr->hash = (Number *)0;
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
Function protoFn_1;
Value *protoFnImpl_9(List *closures, Value *arg0) {
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
FnArity protoFnArity_10 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_9};
Value *protoFnImpl_11(List *closures, Value *arg0, Value *arg1) {
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
FnArity protoFnArity_12 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_11};
Value *protoFnImpl_13(List *closures, Value *arg0, Value *arg1, Value *arg2) {
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
FnArity protoFnArity_14 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_13};
Value *protoFnImpl_15(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3) {
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
FnArity protoFnArity_16 = {FnArityType, -1, 4, (List *)0, 0, protoFnImpl_15};
Value *protoFnImpl_17(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
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
FnArity protoFnArity_18 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_17};
Value *protoFnImpl_19(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5) {
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
FnArity protoFnArity_20 = {FnArityType, -1, 6, (List *)0, 0, protoFnImpl_19};
Value *protoFnImpl_21(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5, Value *arg6) {
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
FnArity protoFnArity_22 = {FnArityType, -1, 7, (List *)0, 0, protoFnImpl_21};
Value *protoFnImpl_23(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4, Value *arg5, Value *arg6, Value *arg7) {
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
FnArity protoFnArity_24 = {FnArityType, -1, 8, (List *)0, 0, protoFnImpl_23};
Function protoFn_1 = {FunctionType, -1, "invoke", 8, {&protoFnArity_10,
&protoFnArity_12,
&protoFnArity_14,
&protoFnArity_16,
&protoFnArity_18,
&protoFnArity_20,
&protoFnArity_22,
&protoFnArity_24}};

ProtoImpls *protoImpls_3;
Function protoFn_4;
Value *protoFnImpl_25(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_3);
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
FnArity protoFnArity_26 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_25};
Function protoFn_4 = {FunctionType, -1, "type-name", 1, {&protoFnArity_26}};

ProtoImpls *protoImpls_6;
Function protoFn_7;
Value *protoFnImpl_27(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_6);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'type-args' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'type-args'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_28 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_27};
Function protoFn_7 = {FunctionType, -1, "type-args", 1, {&protoFnArity_28}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_0 = {1, -1, 9,"ArrayNode"};
Number _num_4 = {2, -1, 4};
Number _num_3 = {2, -1, 3};
Number _num_11 = {2, -1, 11};
Number _num_9 = {2, -1, 9};
Number _num_5 = {2, -1, 5};
Number _num_10 = {2, -1, 10};
Number _num_12 = {2, -1, 12};
Number _num_1 = {2, -1, 1};
Number _num_7 = {2, -1, 7};
Number _num_6 = {2, -1, 6};
Number _num_8 = {2, -1, 8};
Number _num_2 = {2, -1, 2};

// --------- type-name_impl --------------
Function fn_29;
Value *arityImpl_30(List *closures, Value *arg0) {
incRef((Value *)&_str_0);
return((Value *)&_str_0);
};


// --------- type-name_impl main body --------------
Function fn_29 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_30}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_1 = {1, -1, 6,"Symbol"};

// --------- type-name_impl --------------
Function fn_31;
Value *arityImpl_32(List *closures, Value *arg0) {
incRef((Value *)&_str_1);
return((Value *)&_str_1);
};


// --------- type-name_impl main body --------------
Function fn_31 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_32}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_2 = {1, -1, 6,"SubStr"};

// --------- type-name_impl --------------
Function fn_33;
Value *arityImpl_34(List *closures, Value *arg0) {
incRef((Value *)&_str_2);
return((Value *)&_str_2);
};


// --------- type-name_impl main body --------------
Function fn_33 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_34}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_3 = {1, -1, 7,"Keyword"};

// --------- type-name_impl --------------
Function fn_35;
Value *arityImpl_36(List *closures, Value *arg0) {
incRef((Value *)&_str_3);
return((Value *)&_str_3);
};


// --------- type-name_impl main body --------------
Function fn_35 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_36}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_4 = {1, -1, 4,"List"};

// --------- type-name_impl --------------
Function fn_37;
Value *arityImpl_38(List *closures, Value *arg0) {
incRef((Value *)&_str_4);
return((Value *)&_str_4);
};


// --------- type-name_impl main body --------------
Function fn_37 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_38}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_5 = {1, -1, 6,"Number"};

// --------- type-name_impl --------------
Function fn_39;
Value *arityImpl_40(List *closures, Value *arg0) {
incRef((Value *)&_str_5);
return((Value *)&_str_5);
};


// --------- type-name_impl main body --------------
Function fn_39 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_40}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[18];} _str_6 = {1, -1, 17,"BitmapIndexedNode"};

// --------- type-name_impl --------------
Function fn_41;
Value *arityImpl_42(List *closures, Value *arg0) {
incRef((Value *)&_str_6);
return((Value *)&_str_6);
};


// --------- type-name_impl main body --------------
Function fn_41 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_42}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_7 = {1, -1, 6,"String"};

// --------- type-name_impl --------------
Function fn_43;
Value *arityImpl_44(List *closures, Value *arg0) {
incRef((Value *)&_str_7);
return((Value *)&_str_7);
};


// --------- type-name_impl main body --------------
Function fn_43 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_44}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[18];} _str_8 = {1, -1, 17,"HashCollisionNode"};

// --------- type-name_impl --------------
Function fn_45;
Value *arityImpl_46(List *closures, Value *arg0) {
incRef((Value *)&_str_8);
return((Value *)&_str_8);
};


// --------- type-name_impl main body --------------
Function fn_45 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_46}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[9];} _str_9 = {1, -1, 8,"Function"};

// --------- type-name_impl --------------
Function fn_47;
Value *arityImpl_48(List *closures, Value *arg0) {
incRef((Value *)&_str_9);
return((Value *)&_str_9);
};


// --------- type-name_impl main body --------------
Function fn_47 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_48}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_10 = {1, -1, 6,"Opaque"};

// --------- type-name_impl --------------
Function fn_49;
Value *arityImpl_50(List *closures, Value *arg0) {
incRef((Value *)&_str_10);
return((Value *)&_str_10);
};


// --------- type-name_impl main body --------------
Function fn_49 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_50}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_11 = {1, -1, 7,"FnArity"};

// --------- type-name_impl --------------
Function fn_51;
Value *arityImpl_52(List *closures, Value *arg0) {
incRef((Value *)&_str_11);
return((Value *)&_str_11);
};


// --------- type-name_impl main body --------------
Function fn_51 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_52}}};

// forward declaration for 'print-err'
Value *var_53;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_12 = {1, -1, 4,"void"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[5];} _str_13 = {1, -1, 4,"char"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[7];} _str_14 = {1, -1, 6,"char *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[4];} _str_15 = {1, -1, 3,"int"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_16 = {1, -1, 7,"int64_t"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_17 = {1, -1, 52,"typedef struct {int64_t type; int32_t refs;} Value;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_18 = {1, -1, 7,"Value *"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[70];} _str_19 = {1, -1, 69,"typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[83];} _str_20 = {1, -1, 82,"typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[113];} _str_21 = {1, -1, 112,"typedef struct {int64_t type; int32_t refs; int64_t len; Number *hash; Value *source; char *buffer;} SubString;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[102];} _str_22 = {1, -1, 101,"typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[106];} _str_23 = {1, -1, 105,"typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[108];} _str_24 = {1, -1, 107,"typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[58];} _str_25 = {1, -1, 57,"typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[88];} _str_26 = {1, -1, 87,"typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[89];} _str_27 = {1, -1, 88,"typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[65];} _str_28 = {1, -1, 64,"typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[97];} _str_29 = {1, -1, 96,"typedef struct {int64_t type; int32_t refs; int32_t bitmap; Value *array[];} BitmapIndexedNode;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[75];} _str_30 = {1, -1, 74,"typedef struct {int64_t type; int32_t refs; Value *array[32];} ArrayNode;\n"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[96];} _str_31 = {1, -1, 95,"typedef struct {int64_t type; int32_t refs; int16_t count; Value *array[];} HashCollisionNode;\n"};
Value *var_75 = (Value *)&trueVal;;
Value *var_76 = (Value *)&falseVal;;

#include <stdint.h>
#include <memory.h>
#include <pthread.h>

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

void Sha1Update (Sha1Context* Context, void* Buffer, int64_t BufferSize) {
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

int64_t equal(Value *v1, Value *v2) {
  return (isTrue(valsEqual((List *)0, v1, v2)));
}

Value *assoc(Value *, Value *, Value *, Value *, Value *);
Value *get(Value *, Value *, Value *, Value *, Value *);

Value *sha1(Value *);

Value *hashSeq(Value* n, Value *s);

Value *count(Value* n);

// --------- output-to-file --------------
Function fn_77;
Value *arityImpl_78(List *closures, Value *arg0) {
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
    dec_and_free((Value *)arg0Str);
    return((Value *)&trueVal);
};


// --------- output-to-file main body --------------
Function fn_77 = {FunctionType, -1, "output-to-file", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_78}}};


// --------- standard-output --------------
Function fn_80;
Value *arityImpl_81(List *closures) {
outStream = stdout;
    return((Value *)&trueVal);
};


// --------- standard-output main body --------------
Function fn_80 = {FunctionType, -1, "standard-output", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_81}}};


// --------- symkey-name --------------
Function fn_83;
Value *arityImpl_84(List *closures, Value *arg0) {
return(stringValue(((SubString *)arg0)->buffer));
};


// --------- symkey-name main body --------------
Function fn_83 = {FunctionType, -1, "symkey-name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_84}}};


// --------- char-code --------------
Function fn_86;
Value *arityImpl_87(List *closures, Value *arg0) {
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
Function fn_86 = {FunctionType, -1, "char-code", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_87}}};


// --------- symbol --------------
Function fn_89;
Value *arityImpl_90(List *closures, Value *arg0) {
if (arg0->type == StringType) {
        String *s = (String *)arg0;
        SubString *subStr = malloc_substring();
        subStr->type = SymbolType;
        subStr->len = s->len;
        subStr->source = arg0;
        subStr->hash = (Number *)0;
        incRef(arg0);
        subStr->buffer = s->buffer;
        return((Value *)subStr);
      } else if (arg0->type == SubStringType) {
        SubString *s = (SubString *)arg0;
        SubString *subStr = malloc_substring();
        subStr->type = SymbolType;
        subStr->len = s->len;
        subStr->source = arg0;
        subStr->hash = (Number *)0;
        incRef(arg0);
        subStr->buffer = s->buffer;
        return((Value *)subStr);
      } else if (arg0->type == SymbolType) {
        return(arg0);
      }
        abort();
};


// --------- symbol main body --------------
Function fn_89 = {FunctionType, -1, "symbol", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_90}}};


// --------- new-keyword --------------
Function fn_92;
Value *arityImpl_93(List *closures, Value *arg0) {
if (arg0->type == StringType) {
        String *s = (String *)arg0;
        SubString *subStr = malloc_substring();
        subStr->type = KeywordType;
        subStr->len = s->len;
        subStr->source = arg0;
        subStr->hash = (Number *)0;
        incRef(arg0);
        subStr->buffer = s->buffer;
        return((Value *)subStr);
      } else if (arg0->type == SubStringType) {
        SubString *s = (SubString *)arg0;
        SubString *subStr = malloc_substring();
        subStr->type = KeywordType;
        subStr->len = s->len;
        subStr->source = arg0;
        subStr->hash = (Number *)0;
        incRef(arg0);
        subStr->buffer = s->buffer;
        return((Value *)subStr);
      } else
        abort();
};


// --------- new-keyword main body --------------
Function fn_92 = {FunctionType, -1, "new-keyword", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_93}}};


// --------- abort --------------
Function fn_95;
Value *arityImpl_96(List *closures) {
abort();
    return(true);
};


// --------- abort main body --------------
Function fn_95 = {FunctionType, -1, "abort", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_96}}};


// --------- get-type --------------
Function fn_98;
Value *arityImpl_99(List *closures, Value *arg0) {
return(numberValue(arg0->type));};


// --------- get-type main body --------------
Function fn_98 = {FunctionType, -1, "get-type", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_99}}};


// --------- type= --------------
Function fn_101;
Value *arityImpl_102(List *closures, Value *arg0, Value *arg1) {
if (arg0->type == arg1->type)
      return(true);
    else
      return(false);
};


// --------- type= main body --------------
Function fn_101 = {FunctionType, -1, "type=", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_102}}};


// --------- subs --------------
Function fn_104;
Value *arityImpl_105(List *closures, Value *arg0, Value *arg1) {
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

Value *arityImpl_106(List *closures, Value *arg0, Value *arg1, Value *arg2) {
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
Function fn_104 = {FunctionType, -1, "subs", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_105}, &(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_106}}};


// --------- number-str --------------
Function fn_108;
Value *arityImpl_109(List *closures, Value *arg0) {
String *numStr = (String *)my_malloc(sizeof(String) + 10);
    snprintf(numStr->buffer, 9, "%lld", ((Number *)arg0)->numVal);
    numStr->type = StringType;
    numStr->len = strlen(numStr->buffer);
    return((Value *)numStr);
};


// --------- number-str main body --------------
Function fn_108 = {FunctionType, -1, "number-str", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_109}}};


// --------- number= --------------
Function fn_111;
Value *arityImpl_112(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      return(false);
   } else if (((Number *)arg0)->numVal != ((Number *)arg1)->numVal)
      return(false);
   else
      return(true);
};


// --------- number= main body --------------
Function fn_111 = {FunctionType, -1, "number=", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_112}}};


// --------- number-less-than --------------
Function fn_114;
Value *arityImpl_115(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\ninvalid types for 'number-less-than'\n");
      abort();
   } else if (((Number *)arg0)->numVal < ((Number *)arg1)->numVal)
      return(true);
   else
      return(false);
};


// --------- number-less-than main body --------------
Function fn_114 = {FunctionType, -1, "number-less-than", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_115}}};


// --------- add-numbers --------------
Function fn_117;
Value *arityImpl_118(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\ninvalid types for 'add-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal + ((Number *)arg1)->numVal));
};


// --------- add-numbers main body --------------
Function fn_117 = {FunctionType, -1, "add-numbers", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_118}}};


// --------- subtract-numbers --------------
Function fn_120;
Value *arityImpl_121(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\ninvalid types for 'subtract-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal - ((Number *)arg1)->numVal));
};


// --------- subtract-numbers main body --------------
Function fn_120 = {FunctionType, -1, "subtract-numbers", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_121}}};


// --------- mult-numbers --------------
Function fn_123;
Value *arityImpl_124(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type) {
      fprintf(stderr, "\n*** invalid types for 'mult-numbers'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal * ((Number *)arg1)->numVal));
};


// --------- mult-numbers main body --------------
Function fn_123 = {FunctionType, -1, "mult-numbers", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_124}}};


// --------- rem --------------
Function fn_126;
Value *arityImpl_127(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != NumberType ||
        arg1->type != NumberType) {
      fprintf(stderr, "\ninvalid types for 'rem'\n");
      abort();
    } else
      return(numberValue(((Number *)arg0)->numVal %
                         ((Number *)arg1)->numVal));
};


// --------- rem main body --------------
Function fn_126 = {FunctionType, -1, "rem", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_127}}};

Value *var_129 = (Value *)&(List){4,-1,0,0,0};;

// --------- cons --------------
Function fn_130;
Value *arityImpl_131(List *closures, Value *arg0) {
incRef(arg0);
return((Value *)listCons(arg0, empty_list));
};

Value *arityImpl_132(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
incRef(arg1);
return((Value *)listCons(arg0, (List *)arg1));
};


// --------- cons main body --------------
Function fn_130 = {FunctionType, -1, "cons", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_131}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_132}}};


// --------- list-count --------------
Function fn_134;
Value *arityImpl_135(List *closures, Value *arg0) {
if (arg0->type != ListType)
      abort();
    else
      return(numberValue(((List *)arg0)->len));};


// --------- list-count main body --------------
Function fn_134 = {FunctionType, -1, "list-count", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_135}}};


// --------- list-empty? --------------
Function fn_137;
Value *arityImpl_138(List *closures, Value *arg0) {

if (arg0->type != ListType)
{
  fprintf(stderr, "*** 'list-empty?' given wrong type of value\n");
  abort();
}
else if (((List *)arg0)->len == 0)
  return((Value *)&trueVal);
else
  return((Value *)&falseVal);
};


// --------- list-empty? main body --------------
Function fn_137 = {FunctionType, -1, "list-empty?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_138}}};


// --------- car --------------
Function fn_140;
Value *arityImpl_141(List *closures, Value *arg0) {
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
Function fn_140 = {FunctionType, -1, "car", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_141}}};


// --------- cdr --------------
Function fn_143;
Value *arityImpl_144(List *closures, Value *arg0) {
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
Function fn_143 = {FunctionType, -1, "cdr", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_144}}};


// --------- fn-name --------------
Function fn_146;
Value *arityImpl_147(List *closures, Value *arg0) {
if (arg0->type != FunctionType) {
      fprintf(stderr, "\n*** invalid type for 'fn-name'\n");
      abort();
    } else
      return(stringValue(((Function *)arg0)->name));
};


// --------- fn-name main body --------------
Function fn_146 = {FunctionType, -1, "fn-name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_147}}};


// --------- char --------------
Function fn_149;
Value *arityImpl_150(List *closures, Value *arg0) {
if (arg0->type != NumberType) {
      fprintf(stderr, "\ninvalid type for 'char'\n");
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
Function fn_149 = {FunctionType, -1, "char", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_150}}};


// --------- str-count --------------
Function fn_152;
Value *arityImpl_153(List *closures, Value *arg0) {
if (arg0->type != StringType && arg0->type != SubStringType ) {
      fprintf(stderr, "\ninvalid type for 'str-count'\n");
      abort();
    }
   return(numberValue(((String *)arg0)->len));
};


// --------- str-count main body --------------
Function fn_152 = {FunctionType, -1, "str-count", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_153}}};


// --------- str= --------------
Function fn_155;
Value *arityImpl_156(List *closures, Value *arg0, Value *arg1) {
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
Function fn_155 = {FunctionType, -1, "str=", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_156}}};


// --------- symkey= --------------
Function fn_158;
Value *arityImpl_159(List *closures, Value *arg0, Value *arg1) {
if (arg0->type != arg1->type)
      return(false);
    else {
      SubString *s1 = (SubString *)arg0;
      SubString *s2 = (SubString *)arg1;
      if (s1->type == s2->type &&
          s1->len == s2->len &&
          strncmp(s1->buffer, s2->buffer, s1->len) == 0) {
        return(true);
      } else
        return(false);
    }
};


// --------- symkey= main body --------------
Function fn_158 = {FunctionType, -1, "symkey=", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_159}}};


// --------- str-malloc --------------
Function fn_161;
Value *arityImpl_162(List *closures, Value *arg0) {
String *strVal = (String *)my_malloc(sizeof(String) + ((Number *)arg0)->numVal + 5);
    strVal->type = StringType;
    strVal->len = 0;
    strVal->buffer[0] = 0;
    return((Value *)strVal);
};


// --------- str-malloc main body --------------
Function fn_161 = {FunctionType, -1, "str-malloc", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_162}}};


// --------- str-append --------------
Function fn_164;
Value *arityImpl_165(List *closures, Value *arg0, Value *arg1) {
 if (arg0->type != StringType) {
      fprintf(stderr, "\ninvalid type for 'str-append'\n");
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
Function fn_164 = {FunctionType, -1, "str-append", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_165}}};


// --------- pr-err* --------------
Function fn_167;
Value *arityImpl_168(List *closures, Value *arg0) {
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
Function fn_167 = {FunctionType, -1, "pr-err*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_168}}};


// --------- slurp --------------
Function fn_170;
Value *arityImpl_171(List *closures, Value *arg0) {
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
    dec_and_free((Value *)arg0Str);
    return((Value *)strVal);
};


// --------- slurp main body --------------
Function fn_170 = {FunctionType, -1, "slurp", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_171}}};


// --------- fn-apply --------------
Function fn_173;
Value *arityImpl_174(List *closures, Value *arg0, Value *arg1) {
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
Function fn_173 = {FunctionType, -1, "fn-apply", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_174}}};


// --------- escape-chars --------------
Function fn_176;
Value *arityImpl_177(List *closures, Value *arg0) {
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
Function fn_176 = {FunctionType, -1, "escape-chars", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_177}}};


// --------- filter --------------
Function fn_179;
Value *arityImpl_180(List *closures, Value *arg0, Value *arg1) {
List *l = (List *)arg0;
      if (arg0->type != ListType) {
         fprintf(stderr, "'filter' is only defined for 'List' values\n");
         abort();
      }

      if (l->len == 0)
        return((Value *)empty_list);
      else {
        List *head = empty_list;
        List *tail = empty_list;
        for(Value *x = l->head; x != (Value *)0; l = l->tail, x = l->head) {
          Value *y;
          if(arg1->type != 3) {
            y = protoFnImpl_11(empty_list, arg1, x);
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
              dec_and_free((Value *)varArgs3);
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
Function fn_179 = {FunctionType, -1, "filter", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_180}}};


// --------- pr* --------------
Function fn_182;
Value *arityImpl_183(List *closures, Value *arg0) {
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
Function fn_182 = {FunctionType, -1, "pr*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_183}}};


// --------- list --------------
Function fn_185;
Value *arityImpl_186(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_185 = {FunctionType, -1, "list", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_186}}};

Number _num_13 = {2, -1, 0};

// --------- not --------------
Function fn_188;
Value *arityImpl_189(List *closures, Value *arg0) {
Value *cond1;

if (isTrue(arg0)) {
dec_and_free(arg0);
incRef((Value *)&_num_13);
cond1 = (Value *)&_num_13;
} else {
dec_and_free(arg0);
incRef((Value *)&_num_1);
cond1 = (Value *)&_num_1;
}
return(cond1);
};


// --------- not main body --------------
Function fn_188 = {FunctionType, -1, "not", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_189}}};


// --------- remove --------------
Function fn_191;

// --------- anon --------------
Function fn_193;
Value *arityImpl_194(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt5;
if((val1)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, val1, arg0);
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
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val1)->name);
  abort();
}
}
Value *rslt6 = arityImpl_189(empty_list, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};

Value *arityImpl_192(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_194;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_193 = malloc_function(1);
fn_193->type = FunctionType;
fn_193->name = "anon";
fn_193->arityCount = 1;
fn_193->arities[0] = arity_2;
Value *rslt3 = arityImpl_180(empty_list, arg0, (Value *)fn_193);
incRef(rslt3);
dec_and_free((Value *)fn_193);
dec_and_free(rslt3);
return(rslt3);
};


// --------- remove main body --------------
Function fn_191 = {FunctionType, -1, "remove", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_192}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_32 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_196;
Function protoFn_197;
Value *arityImpl_199(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_32, arg0);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_32, arg0);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
incRef((Value *)&_str_32);
varArgs3 = (List *)listCons((Value *)&_str_32, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt6 = arityImpl_96(empty_list);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};

Value *protoFnImpl_200(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_196);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '<*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_201 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_200};
Function defaultFn_198 = {FunctionType, -1, "<*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_199}}};

Function protoFn_197 = {FunctionType, -1, "<*", 1, {&protoFnArity_201}};

ProtoImpls *protoImpls_202;
Function protoFn_203;
Value *protoFnImpl_220(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_202);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'empty' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_221 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_220};
Function protoFn_203 = {FunctionType, -1, "empty", 1, {&protoFnArity_221}};

ProtoImpls *protoImpls_205;
Function protoFn_206;
Value *protoFnImpl_222(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_205);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'count' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_223 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_222};
Function protoFn_206 = {FunctionType, -1, "count", 1, {&protoFnArity_223}};

ProtoImpls *protoImpls_208;
Function protoFn_209;
Value *protoFnImpl_224(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_208);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'conj' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_225 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_224};
Function protoFn_209 = {FunctionType, -1, "conj", 1, {&protoFnArity_225}};

ProtoImpls *protoImpls_211;
Function protoFn_212;
Value *protoFnImpl_226(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_211);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'destruct' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_227 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_226};
Function protoFn_212 = {FunctionType, -1, "destruct", 1, {&protoFnArity_227}};

ProtoImpls *protoImpls_214;
Function protoFn_215;
Value *protoFnImpl_228(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_214);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'empty?' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_229 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_228};
Function protoFn_215 = {FunctionType, -1, "empty?", 1, {&protoFnArity_229}};

ProtoImpls *protoImpls_217;
Function protoFn_218;
Value *protoFnImpl_230(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_217);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'reduce' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_231 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_230};
Function protoFn_218 = {FunctionType, -1, "reduce", 1, {&protoFnArity_231}};


// --------- reverse --------------
Function fn_232;
Value *arityImpl_233(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_220(empty_list, arg0);
Value *rslt2 = protoFnImpl_230(empty_list, arg0, rslt1, (Value *)&protoFn_209);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- reverse main body --------------
Function fn_232 = {FunctionType, -1, "reverse", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_233}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_33 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_235;
Function protoFn_236;
Value *arityImpl_238(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_25(empty_list, arg0);
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_33, rslt1);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_33, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
incRef((Value *)&_str_33);
varArgs3 = (List *)listCons((Value *)&_str_33, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt6 = arityImpl_96(empty_list);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
return(rslt6);
};

Value *protoFnImpl_239(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_235);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'string-list' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_240 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_239};
Function defaultFn_237 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_238}}};

Function protoFn_236 = {FunctionType, -1, "string-list", 1, {&protoFnArity_240}};

ProtoImpls *protoImpls_241;
Function protoFn_242;
Value *arityImpl_244(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt3 = arityImpl_102(empty_list, arg0, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
Value *rslt4 = protoFnImpl_27(empty_list, arg0);
Value *rslt5 = protoFnImpl_27(empty_list, arg1);
Value *rslt9;
FnArity *arity6 = findFnArity((Value *)&protoFn_242, 2);
if(arity6 != (FnArity *)0 && !arity6->variadic) {
FnType2 *fn8 = (FnType2 *)arity6->fn;
rslt9 = fn8(arity6->closures, rslt4, rslt5);
} else if(arity6 != (FnArity *)0 && arity6->variadic) {
FnType1 *fn8 = (FnType1 *)arity6->fn;
List *varArgs7 = empty_list;
incRef(rslt5);
varArgs7 = (List *)listCons(rslt5, varArgs7);
incRef(rslt4);
varArgs7 = (List *)listCons(rslt4, varArgs7);
rslt9 = fn8(arity6->closures, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&protoFn_242)->name);
  abort();
}
incRef(rslt9);
cond2 = rslt9;
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt4);
} else {
dec_and_free(rslt3);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
}
return(cond2);
};

Value *protoFnImpl_245(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_241);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '=*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_246 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_245};
Function defaultFn_243 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_244}}};

Function protoFn_242 = {FunctionType, -1, "=*", 1, {&protoFnArity_246}};

ProtoImpls *protoImpls_247;
Function protoFn_248;
Value *protoFnImpl_250(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_247);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'sha1' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_251 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_250};
Function protoFn_248 = {FunctionType, -1, "sha1", 1, {&protoFnArity_251}};


// --------- sha1_impl --------------
Function fn_252;
Value *arityImpl_257(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
Number *numVal = (Number *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)&numVal->type, 8);
Sha1Update(&context, (void *)&numVal->numVal, 8);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_252 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_257}}};


// --------- <*_impl --------------
Function fn_253;
Value *arityImpl_258(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_115(empty_list, arg0, arg1);
return(rslt2);
};


// --------- <*_impl main body --------------
Function fn_253 = {FunctionType, -1, "<*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_258}}};


// --------- =*_impl --------------
Function fn_254;
Value *arityImpl_259(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_112(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_254 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_259}}};


// --------- string-list_impl --------------
Function fn_255;
Value *arityImpl_260(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_109(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_255 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_260}}};


// --------- type-args_impl --------------
Function fn_256;
Value *arityImpl_261(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- type-args_impl main body --------------
Function fn_256 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_261}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_34 = {1, -1, 52,"*** call to 'instance?' with unknown type parameter."};
ProtoImpls *protoImpls_262;
Function protoFn_263;
Value *arityImpl_265(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt5 = arityImpl_99(empty_list, arg0);
Value *rslt6 = arityImpl_112(empty_list, (Value *)&_num_2, rslt5);
dec_and_free(rslt5);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *rslt7 = arityImpl_99(empty_list, arg1);
Value *rslt8 = arityImpl_112(empty_list, arg0, rslt7);
incRef(rslt8);
cond2 = rslt8;
dec_and_free(rslt8);
dec_and_free(rslt7);
} else {
dec_and_free(rslt6);
Value *rslt3 = arityImpl_183(empty_list, (Value *)&_str_34);
Value *rslt4 = arityImpl_96(empty_list);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};

Value *protoFnImpl_266(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_262);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'instance?' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_267 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_266};
Function defaultFn_264 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_265}}};

Function protoFn_263 = {FunctionType, -1, "instance?", 1, {&protoFnArity_267}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_35 = {1, -1, 28,"'flat-map' not implemented: "};
ProtoImpls *protoImpls_268;
Function protoFn_269;
Value *arityImpl_274(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_25(empty_list, arg0);
Value *rslt6;
if((var_53)->type != FunctionType) {
rslt6 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_35, rslt2);
} else {
FnArity *arity3 = findFnArity(var_53, 2);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType2 *fn5 = (FnType2 *)arity3->fn;
rslt6 = fn5(arity3->closures, (Value *)&_str_35, rslt2);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(rslt2);
varArgs4 = (List *)listCons(rslt2, varArgs4);
incRef((Value *)&_str_35);
varArgs4 = (List *)listCons((Value *)&_str_35, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt7 = arityImpl_96(empty_list);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt7);
dec_and_free(rslt2);
return(rslt7);
};

Value *protoFnImpl_275(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_268);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'flat-map' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_276 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_275};
Function defaultFn_270 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_274}}};

Function protoFn_269 = {FunctionType, -1, "flat-map", 1, {&protoFnArity_276}};

ProtoImpls *protoImpls_271;
Function protoFn_272;

// --------- anon --------------
Function fn_278;
Value *arityImpl_279(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- anon main body --------------
Function fn_278 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_279}}};

Value *arityImpl_277(List *closures, Value *arg0) {
Value *rslt2 = protoFnImpl_275(empty_list, arg0, (Value *)&fn_278);
return(rslt2);
};

Value *protoFnImpl_280(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_271);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'flatten' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_281 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_280};
Function defaultFn_273 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_277}}};

Function protoFn_272 = {FunctionType, -1, "flatten", 1, {&protoFnArity_281}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[30];} _str_36 = {1, -1, 29,"'duplicate' not implemented: "};
ProtoImpls *protoImpls_282;
Function protoFn_283;
Value *protoFnImpl_291(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_282);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'extend' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_292 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_291};
Function protoFn_283 = {FunctionType, -1, "extend", 1, {&protoFnArity_292}};

ProtoImpls *protoImpls_285;
Function protoFn_286;
Value *arityImpl_293(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_25(empty_list, arg0);
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_36, rslt1);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_36, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
incRef((Value *)&_str_36);
varArgs3 = (List *)listCons((Value *)&_str_36, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
incRef(rslt5);
dec_and_free(rslt1);
dec_and_free(rslt5);
return(rslt5);
};

Value *protoFnImpl_294(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_285);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'duplicate' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_295 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_294};
Function defaultFn_287 = {FunctionType, -1, "duplicate", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_293}}};

Function protoFn_286 = {FunctionType, -1, "duplicate", 1, {&protoFnArity_295}};

ProtoImpls *protoImpls_288;
Function protoFn_289;
Value *protoFnImpl_296(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_288);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'extract' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_297 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_296};
Function protoFn_289 = {FunctionType, -1, "extract", 1, {&protoFnArity_297}};

// forward declaration for 'comprehend'
Value *var_298;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_37 = {1, -1, 26,"*** 'wrap' not implemented"};
ProtoImpls *protoImpls_299;
Function protoFn_300;
Value *arityImpl_305(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, var_53, (Value *)&_str_37);
} else {
FnArity *arity2 = findFnArity(var_53, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_37);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef((Value *)&_str_37);
varArgs3 = (List *)listCons((Value *)&_str_37, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
return(rslt5);
};

Value *protoFnImpl_306(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_299);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'wrap' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_307 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_306};
Function defaultFn_301 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_305}}};

Function protoFn_300 = {FunctionType, -1, "wrap", 1, {&protoFnArity_307}};

ProtoImpls *protoImpls_302;
Function protoFn_303;

// --------- anon --------------
Function fn_312;
Value *arityImpl_313(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt5;
if((arg0)->type != FunctionType) {
rslt5 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity2 = findFnArity(arg0, 0);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType0 *fn4 = (FnType0 *)arity2->fn;
rslt5 = fn4(arity2->closures);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
Value *rslt6 = protoFnImpl_306(empty_list, val1, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};


// --------- anon --------------
Function fn_314;
Value *arityImpl_315(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt5;
if((var_298)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_298, arg0, val1);
} else {
FnArity *arity2 = findFnArity(var_298, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, arg0, val1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(val1);
varArgs3 = (List *)listCons(val1, varArgs3);
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_298)->name);
  abort();
}
}
return(rslt5);
};

Value *arityImpl_308(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond6;
Value *rslt7 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
Value *cond8;
Value *rslt9 = protoFnImpl_222(empty_list, rslt2);
Value *rslt10 = protoFnImpl_200(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_76);
cond8 = var_76;
} else {
dec_and_free(rslt10);
incRef(var_75);
cond8 = var_75;
}
incRef(cond8);
cond6 = cond8;
dec_and_free(cond8);
} else {
dec_and_free(rslt7);
incRef(var_76);
cond6 = var_76;
}

if (isTrue(cond6)) {
dec_and_free(cond6);
List *arg13 = (List *)rslt2;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
FnArity *arity_14 = malloc_fnArity();
arity_14->type = FnArityType;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_315;
incRef((Value *)arg1);
arity_14->closures = listCons((Value *)arg1, (List *)arity_14->closures);
Function *fn_314 = malloc_function(1);
fn_314->type = FunctionType;
fn_314->name = "anon";
fn_314->arityCount = 1;
fn_314->arities[0] = arity_14;
Value *rslt15 = protoFnImpl_275(empty_list, arg0, (Value *)fn_314);
incRef(rslt15);
cond3 = rslt15;
dec_and_free(rslt15);
dec_and_free((Value *)fn_314);
} else {
dec_and_free(cond6);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = FnArityType;
arity_4->count = 1;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_313;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
Function *fn_312 = malloc_function(1);
fn_312->type = FunctionType;
fn_312->name = "anon";
fn_312->arityCount = 1;
fn_312->arities[0] = arity_4;
Value *rslt5 = protoFnImpl_275(empty_list, arg0, (Value *)fn_312);
incRef(rslt5);
cond3 = rslt5;
dec_and_free((Value *)fn_312);
dec_and_free(rslt5);
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};

Value *protoFnImpl_316(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_302);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'apply*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_317 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_316};
Function defaultFn_304 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_308}}};

Function protoFn_303 = {FunctionType, -1, "apply*", 1, {&protoFnArity_317}};


// --------- comprehend --------------
Function fn_319;

// --------- anon --------------
Function fn_321;
Value *arityImpl_323(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val3  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4 = arityImpl_132(empty_list, arg1, arg0);
Value *rslt5 = arityImpl_233(empty_list, rslt4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
Value *rslt7 = arityImpl_186(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = protoFnImpl_316(empty_list, val3, rslt7);
Value *rslt9 = protoFnImpl_306(empty_list, val2, rslt8);
incRef(rslt9);
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt9);
};


// --------- anon --------------
Function fn_322;

// --------- anon --------------
Function fn_325;

// --------- anon --------------
Function fn_327;
Value *arityImpl_328(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val3  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4 = arityImpl_132(empty_list, val2, val3);
Value *rslt8;
if((val1)->type != FunctionType) {
rslt8 = protoFnImpl_11(empty_list, val1, rslt4);
} else {
FnArity *arity5 = findFnArity(val1, 1);
if(arity5 != (FnArity *)0 && !arity5->variadic) {
FnType1 *fn7 = (FnType1 *)arity5->fn;
rslt8 = fn7(arity5->closures, rslt4);
} else if(arity5 != (FnArity *)0 && arity5->variadic) {
FnType1 *fn7 = (FnType1 *)arity5->fn;
List *varArgs6 = empty_list;
incRef(rslt4);
varArgs6 = (List *)listCons(rslt4, varArgs6);
rslt8 = fn7(arity5->closures, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val1)->name);
  abort();
}
}
incRef(arg0);
dec_and_free(rslt8);
dec_and_free(rslt4);
return(arg0);
};

Value *arityImpl_326(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val4  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_328;
incRef((Value *)arg0);
arity_3->closures = listCons((Value *)arg0, (List *)arity_3->closures);
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
incRef((Value *)val4);
arity_3->closures = listCons((Value *)val4, (List *)arity_3->closures);
Function *fn_327 = malloc_function(1);
fn_327->type = FunctionType;
fn_327->name = "anon";
fn_327->arityCount = 1;
fn_327->arities[0] = arity_3;
Value *rslt5 = protoFnImpl_275(empty_list, val2, (Value *)fn_327);
incRef(rslt5);
dec_and_free(rslt5);
dec_and_free((Value *)fn_327);
return(rslt5);
};

Value *arityImpl_324(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 2;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_326;
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_325 = malloc_function(1);
fn_325->type = FunctionType;
fn_325->name = "anon";
fn_325->arityCount = 1;
fn_325->arities[0] = arity_2;
return((Value *)fn_325);
};


// --------- anon main body --------------
Function fn_322 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_324}}};


// --------- anon --------------
Function fn_329;
Value *arityImpl_330(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt5;
if((val1)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, val1, var_129, arg0);
} else {
FnArity *arity2 = findFnArity(val1, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, var_129, arg0);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
incRef(var_129);
varArgs3 = (List *)listCons(var_129, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val1)->name);
  abort();
}
}
return(rslt5);
};

Value *arityImpl_320(List *closures, Value *arg0, Value *arg3) {
List *arg4 = (List *)arg3;
Value *arg1 = arg4->head;
if (arg4->tail) arg4->tail->len = arg4->len - 1;
arg4 = arg4->tail;
Value *arg2 = (Value *) arg4;
Value *rslt5 = arityImpl_233(empty_list, arg2);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 2;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_323;
incRef((Value *)arg0);
arity_6->closures = listCons((Value *)arg0, (List *)arity_6->closures);
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_321 = malloc_function(1);
fn_321->type = FunctionType;
fn_321->name = "anon";
fn_321->arityCount = 1;
fn_321->arities[0] = arity_6;
Value *rslt8 = protoFnImpl_230(empty_list, rslt5, (Value *)fn_321, (Value *)&fn_322);
FnArity *arity_9 = malloc_fnArity();
arity_9->type = FnArityType;
arity_9->count = 1;
arity_9->closures = empty_list;
arity_9->variadic = 0;
arity_9->fn = arityImpl_330;
incRef((Value *)rslt8);
arity_9->closures = listCons((Value *)rslt8, (List *)arity_9->closures);
Function *fn_329 = malloc_function(1);
fn_329->type = FunctionType;
fn_329->name = "anon";
fn_329->arityCount = 1;
fn_329->arities[0] = arity_9;
Value *rslt10 = protoFnImpl_275(empty_list, arg1, (Value *)fn_329);
incRef(rslt10);
dec_and_free((Value *)fn_321);
dec_and_free(rslt8);
dec_and_free(rslt10);
dec_and_free((Value *)fn_329);
dec_and_free(rslt5);
return(rslt10);
};


// --------- comprehend main body --------------
Function fn_319 = {FunctionType, -1, "comprehend", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_320}}};

Value *var_298 = (Value *)&fn_319;
ProtoImpls *protoImpls_331;
Function protoFn_332;

// --------- anon --------------
Function fn_335;
Value *arityImpl_336(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt6;
if((val2)->type != FunctionType) {
rslt6 = protoFnImpl_11(empty_list, val2, arg0);
} else {
FnArity *arity3 = findFnArity(val2, 1);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
rslt6 = fn5(arity3->closures, arg0);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(arg0);
varArgs4 = (List *)listCons(arg0, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val2)->name);
  abort();
}
}
Value *rslt7 = protoFnImpl_306(empty_list, val1, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt7);
return(rslt7);
};

Value *arityImpl_334(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_336;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
Function *fn_335 = malloc_function(1);
fn_335->type = FunctionType;
fn_335->name = "anon";
fn_335->arityCount = 1;
fn_335->arities[0] = arity_2;
Value *rslt3 = protoFnImpl_275(empty_list, arg0, (Value *)fn_335);
incRef(rslt3);
dec_and_free((Value *)fn_335);
dec_and_free(rslt3);
return(rslt3);
};

Value *protoFnImpl_337(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_331);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'map' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_338 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_337};
Function defaultFn_333 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_334}}};

Function protoFn_332 = {FunctionType, -1, "map", 1, {&protoFnArity_338}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_38 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_339;
Function protoFn_340;
Value *arityImpl_342(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_25(empty_list, arg0);
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_38, rslt1);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_38, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
incRef((Value *)&_str_38);
varArgs3 = (List *)listCons((Value *)&_str_38, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt6 = arityImpl_96(empty_list);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
return(rslt6);
};

Value *protoFnImpl_343(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_339);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'name' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_344 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_343};
Function defaultFn_341 = {FunctionType, -1, "name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_342}}};

Function protoFn_340 = {FunctionType, -1, "name", 1, {&protoFnArity_344}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_39 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_345;
Function protoFn_346;
Value *arityImpl_348(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_25(empty_list, arg0);
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_39, rslt1);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_39, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
incRef((Value *)&_str_39);
varArgs3 = (List *)listCons((Value *)&_str_39, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt6 = arityImpl_96(empty_list);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
return(rslt6);
};

Value *protoFnImpl_349(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_345);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'serialize' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_350 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_349};
Function defaultFn_347 = {FunctionType, -1, "serialize", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_348}}};

Function protoFn_346 = {FunctionType, -1, "serialize", 1, {&protoFnArity_350}};

ProtoImpls *protoImpls_351;
Function protoFn_352;
Value *protoFnImpl_366(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_351);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'rest' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_367 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_366};
Function protoFn_352 = {FunctionType, -1, "rest", 1, {&protoFnArity_367}};

ProtoImpls *protoImpls_354;
Function protoFn_355;
Value *protoFnImpl_368(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_354);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'seq' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_369 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_368};
Function protoFn_355 = {FunctionType, -1, "seq", 1, {&protoFnArity_369}};

ProtoImpls *protoImpls_357;
Function protoFn_358;
Value *protoFnImpl_370(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_357);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'first' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_371 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_370};
Function protoFn_358 = {FunctionType, -1, "first", 1, {&protoFnArity_371}};

ProtoImpls *protoImpls_360;
Function protoFn_361;
Value *protoFnImpl_372(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_360);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'm-first' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 1);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'm-first'\n");
    abort();
}
  FnType1 *_fn = (FnType1 *)_arity->fn;
  return(_fn(_arity->closures, arg0));
}
FnArity protoFnArity_373 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_372};
Function protoFn_361 = {FunctionType, -1, "m-first", 1, {&protoFnArity_373}};

ProtoImpls *protoImpls_363;
Function protoFn_364;
Value *arityImpl_374(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};

Value *protoFnImpl_375(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_363);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'seq?' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_376 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_375};
Function defaultFn_365 = {FunctionType, -1, "seq?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_374}}};

Function protoFn_364 = {FunctionType, -1, "seq?", 1, {&protoFnArity_376}};


// --------- second --------------
Function fn_377;
Value *arityImpl_378(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_366(empty_list, arg0);
Value *rslt2 = protoFnImpl_370(empty_list, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- second main body --------------
Function fn_377 = {FunctionType, -1, "second", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_378}}};

ProtoImpls *protoImpls_380;
Function protoFn_381;
Value *protoFnImpl_383(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_380);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'traverse' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_384 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_383};
Function protoFn_381 = {FunctionType, -1, "traverse", 1, {&protoFnArity_384}};

ProtoImpls *protoImpls_385;
Function protoFn_386;
Value *protoFnImpl_388(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_385);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'crush' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_389 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_388};
Function protoFn_386 = {FunctionType, -1, "crush", 1, {&protoFnArity_389}};

ProtoImpls *protoImpls_390;
Function protoFn_391;
Value *protoFnImpl_396(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_390);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'comp*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_397 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_396};
Function protoFn_391 = {FunctionType, -1, "comp*", 1, {&protoFnArity_397}};

ProtoImpls *protoImpls_393;
Function protoFn_394;
Value *protoFnImpl_398(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_393);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'zero' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_399 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_398};
Function protoFn_394 = {FunctionType, -1, "zero", 1, {&protoFnArity_399}};


// --------- apply --------------
Function fn_400;
Value *arityImpl_401(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = protoFnImpl_316(empty_list, arg0, arg1);
return(rslt2);
};

// --------- apply main body --------------
Function fn_400 = {FunctionType, -1, "apply", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_401}}};


// --------- apply-to --------------
Function fn_403;
Value *arityImpl_404(List *closures, Value *arg0) {
Value *rslt4;
if((arg0)->type != FunctionType) {
rslt4 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity1 = findFnArity(arg0, 0);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType0 *fn3 = (FnType0 *)arity1->fn;
rslt4 = fn3(arity1->closures);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
return(rslt4);
};

Value *arityImpl_405(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = arityImpl_141(empty_list, arg1);
Value *rslt3 = protoFnImpl_306(empty_list, rslt2, arg0);
Value *rslt4 = protoFnImpl_316(empty_list, rslt3, arg1);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- apply-to main body --------------
Function fn_403 = {FunctionType, -1, "apply-to", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_404}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_405}}};


// --------- comp --------------
Function fn_407;
Value *arityImpl_408(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_409(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = protoFnImpl_396(empty_list, arg0, arg1);
return(rslt2);
};

// --------- comp main body --------------
Function fn_407 = {FunctionType, -1, "comp", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_408}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_409}}};

ProtoImpls *protoImpls_411;
Function protoFn_412;
Value *protoFnImpl_420(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_411);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'get*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 5);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'get*'\n");
    abort();
}
  FnType5 *_fn = (FnType5 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1, arg2, arg3, arg4));
}
FnArity protoFnArity_421 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_420};
Function protoFn_412 = {FunctionType, -1, "get*", 1, {&protoFnArity_421}};

ProtoImpls *protoImpls_414;
Function protoFn_415;
Value *protoFnImpl_422(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_414);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'assoc*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_423 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_422};
Function protoFn_415 = {FunctionType, -1, "assoc*", 1, {&protoFnArity_423}};

ProtoImpls *protoImpls_417;
Function protoFn_418;
Value *protoFnImpl_424(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_417);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'hash-seq' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_425 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_424};
Function protoFn_418 = {FunctionType, -1, "hash-seq", 1, {&protoFnArity_425}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[26];} _str_40 = {1, -1, 25,"'get' not implemented for"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_41 = {1, -1, 2,": "};
SubString _kw_1 = {5, -1, 2, 0, 0, ":k"};
SubString _kw_0 = {5, -1, 2, 0, 0, ":m"};
ProtoImpls *protoImpls_426;
Function protoFn_427;
Value *protoFnImpl_441(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_426);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'assoc' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_442 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_441};
Function protoFn_427 = {FunctionType, -1, "assoc", 1, {&protoFnArity_442}};

ProtoImpls *protoImpls_429;
Function protoFn_430;
Value *protoFnImpl_443(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_429);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'dissoc' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
abort();
}
  FnArity *_arity = findFnArity((Value *)implFn, 2);
  if(_arity == (FnArity *)0 || _arity->variadic) {
    fprintf(stderr, "\n*** Invalid number of args in call to 'dissoc'\n");
    abort();
}
  FnType2 *_fn = (FnType2 *)_arity->fn;
  return(_fn(_arity->closures, arg0, arg1));
}
FnArity protoFnArity_444 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_443};
Function protoFn_430 = {FunctionType, -1, "dissoc", 1, {&protoFnArity_444}};

ProtoImpls *protoImpls_432;
Function protoFn_433;
Value *protoFnImpl_445(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_432);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'vals' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_446 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_445};
Function protoFn_433 = {FunctionType, -1, "vals", 1, {&protoFnArity_446}};

ProtoImpls *protoImpls_435;
Function protoFn_436;
Value *arityImpl_447(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_25(empty_list, arg0);
Value *rslt7;
if((var_53)->type != FunctionType) {
rslt7 = protoFnImpl_23(empty_list, var_53, (Value *)&_str_40, rslt3, (Value *)&_str_41, (Value *)&_kw_0, arg0, (Value *)&_kw_1, arg1);
} else {
FnArity *arity4 = findFnArity(var_53, 7);
if(arity4 != (FnArity *)0 && !arity4->variadic) {
FnType7 *fn6 = (FnType7 *)arity4->fn;
rslt7 = fn6(arity4->closures, (Value *)&_str_40, rslt3, (Value *)&_str_41, (Value *)&_kw_0, arg0, (Value *)&_kw_1, arg1);
} else if(arity4 != (FnArity *)0 && arity4->variadic) {
FnType1 *fn6 = (FnType1 *)arity4->fn;
List *varArgs5 = empty_list;
incRef(arg1);
varArgs5 = (List *)listCons(arg1, varArgs5);
incRef((Value *)&_kw_1);
varArgs5 = (List *)listCons((Value *)&_kw_1, varArgs5);
incRef(arg0);
varArgs5 = (List *)listCons(arg0, varArgs5);
incRef((Value *)&_kw_0);
varArgs5 = (List *)listCons((Value *)&_kw_0, varArgs5);
incRef((Value *)&_str_41);
varArgs5 = (List *)listCons((Value *)&_str_41, varArgs5);
incRef(rslt3);
varArgs5 = (List *)listCons(rslt3, varArgs5);
incRef((Value *)&_str_40);
varArgs5 = (List *)listCons((Value *)&_str_40, varArgs5);
rslt7 = fn6(arity4->closures, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt8 = arityImpl_96(empty_list);
incRef(rslt8);
dec_and_free(rslt8);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt8);
};

Value *protoFnImpl_448(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_435);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'get' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_449 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_448};
Function defaultFn_437 = {FunctionType, -1, "get", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_447}}};

Function protoFn_436 = {FunctionType, -1, "get", 1, {&protoFnArity_449}};

ProtoImpls *protoImpls_438;
Function protoFn_439;
Value *protoFnImpl_450(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_438);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'keys' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_451 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_450};
Function protoFn_439 = {FunctionType, -1, "keys", 1, {&protoFnArity_451}};


// --------- and --------------
Function fn_452;
Value *arityImpl_453(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_454(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;

if (isTrue(arg0)) {
dec_and_free(arg0);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_186(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_316(empty_list, (Value *)&fn_452, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
} else {
dec_and_free(arg0);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
}
return(cond2);
};

// --------- and main body --------------
Function fn_452 = {FunctionType, -1, "and", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_453}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_454}}};


// --------- or --------------
Function fn_456;
Value *arityImpl_457(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_458(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;

if (isTrue(arg0)) {
dec_and_free(arg0);
incRef((Value *)&_num_1);
cond2 = (Value *)&_num_1;
} else {
dec_and_free(arg0);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_186(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_316(empty_list, (Value *)&fn_456, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
return(cond2);
};

// --------- or main body --------------
Function fn_456 = {FunctionType, -1, "or", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_457}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_458}}};


// --------- = --------------
Function fn_460;
Value *arityImpl_461(List *closures, Value *arg0) {
incRef((Value *)&_num_1);
return((Value *)&_num_1);
};

Value *arityImpl_462(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_245(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_463(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;
Value *rslt3 = arityImpl_141(empty_list, arg1);
Value *rslt4 = protoFnImpl_245(empty_list, arg0, rslt3);
dec_and_free(rslt3);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)arg1);
varArgs5 = (List *)listCons((Value *)arg1, varArgs5);
Value *rslt6 = arityImpl_186(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_316(empty_list, (Value *)&fn_460, rslt6);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
} else {
dec_and_free(rslt4);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
}
return(cond2);
};

// --------- = main body --------------
Function fn_460 = {FunctionType, -1, "=", 3, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_461}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_462}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_463}}};


// --------- partial --------------
Function fn_465;

// --------- anon --------------
Function fn_467;
Value *arityImpl_468(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
Value *rslt4 = arityImpl_186(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_396(empty_list, val2, rslt4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
Value *rslt7 = arityImpl_186(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = protoFnImpl_316(empty_list, val1, rslt7);
incRef(rslt8);
dec_and_free(rslt8);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt8);
};
Value *arityImpl_466(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 2;
arity_2->closures = empty_list;
arity_2->variadic = 1;
arity_2->fn = arityImpl_468;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
Function *fn_467 = malloc_function(1);
fn_467->type = FunctionType;
fn_467->name = "anon";
fn_467->arityCount = 1;
fn_467->arities[0] = arity_2;
return((Value *)fn_467);
};

// --------- partial main body --------------
Function fn_465 = {FunctionType, -1, "partial", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_466}}};

// forward declaration for 'maybe-val'
Value *var_470;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_44 = {1, -1, 1,"&"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_43 = {1, -1, 9,"<nothing>"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_42 = {1, -1, 7,"nothing"};

// --------- flatten_impl --------------
Function fn_472;
Value *arityImpl_495(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- flatten_impl main body --------------
Function fn_472 = {FunctionType, -1, "flatten_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_495}}};

Value *protoImpl_496(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_471 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_496}}};


// --------- flat-map_impl --------------
Function fn_474;
Value *arityImpl_497(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- flat-map_impl main body --------------
Function fn_474 = {FunctionType, -1, "flat-map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_497}}};

Value *protoImpl_498(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_473 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_498}}};


// --------- wrap_impl --------------
Function fn_476;
Value *arityImpl_499(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((var_470)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, var_470, arg1);
} else {
FnArity *arity2 = findFnArity(var_470, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, arg1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg1);
varArgs3 = (List *)listCons(arg1, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_470)->name);
  abort();
}
}
return(rslt5);
};


// --------- wrap_impl main body --------------
Function fn_476 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_499}}};

Value *protoImpl_500(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_475 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_500}}};


// --------- apply*_impl --------------
Function fn_478;
Value *arityImpl_501(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- apply*_impl main body --------------
Function fn_478 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_501}}};

Value *protoImpl_502(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_477 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_502}}};


// --------- zero_impl --------------
Function fn_480;
Value *arityImpl_503(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- zero_impl main body --------------
Function fn_480 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_503}}};

Value *protoImpl_504(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_479 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_504}}};


// --------- comp*_impl --------------
Function fn_482;
Value *arityImpl_505(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond4 = cond6;
dec_and_free(cond6);
} else {
dec_and_free(rslt5);
incRef(var_76);
cond4 = var_76;
}

if (isTrue(cond4)) {
dec_and_free(cond4);
List *arg11 = (List *)rslt2;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
Value *rslt12 = protoFnImpl_396(empty_list, arg9, arg10);
incRef(rslt12);
cond3 = rslt12;
dec_and_free(rslt12);
} else {
dec_and_free(cond4);
incRef(arg0);
cond3 = arg0;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- comp*_impl main body --------------
Function fn_482 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_505}}};

Value *protoImpl_509(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_481 = {FunctionType, -1, "comp*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_509}}};


// --------- =*_impl --------------
Function fn_484;
Value *arityImpl_510(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_102(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_484 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_510}}};

Value *protoImpl_511(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_483 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_511}}};


// --------- string-list_impl --------------
Function fn_486;
Value *arityImpl_512(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_43);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_43, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_486 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_512}}};

Value *protoImpl_513(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_485 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_513}}};


// --------- map_impl --------------
Function fn_488;
Value *arityImpl_514(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- map_impl main body --------------
Function fn_488 = {FunctionType, -1, "map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_514}}};

Value *protoImpl_515(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_487 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_515}}};


// --------- type-name_impl --------------
Function fn_490;
Value *arityImpl_516(List *closures, Value *arg0) {
incRef((Value *)&_str_42);
return((Value *)&_str_42);
};


// --------- type-name_impl main body --------------
Function fn_490 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_516}}};

Value *protoImpl_517(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_489 = {FunctionType, -1, "type-name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_517}}};


// --------- type-args_impl --------------
Function fn_492;
Value *arityImpl_518(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- type-args_impl main body --------------
Function fn_492 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_518}}};

Value *protoImpl_519(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_491 = {FunctionType, -1, "type-args", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_519}}};


// --------- invoke_impl --------------
Function fn_494;
Value *arityImpl_520(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- invoke_impl main body --------------
Function fn_494 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_520}}};

Value *protoImpl_521(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[11])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_493 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_521}}};

ReifiedVal reified_522 = {13, -1, 12, {(Value *)&fn_472, (Value *)&fn_474, (Value *)&fn_476, (Value *)&fn_478, (Value *)&fn_480, (Value *)&fn_482, (Value *)&fn_484, (Value *)&fn_486, (Value *)&fn_488, (Value *)&fn_490, (Value *)&fn_492, (Value *)&fn_494}};
ProtoImpls *protoImpls_524;
Function protoFn_525;
Value *protoFnImpl_527(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_524);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for '.v' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_528 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_527};
Function protoFn_525 = {FunctionType, -1, ".v", 1, {&protoFnArity_528}};

Value *protoFnImpl_530(List *, Value *, Value *);
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_45 = {1, -1, 7,"<maybe "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_47 = {1, -1, 9,"maybe-val"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_46 = {1, -1, 1,">"};
Number _num_14 = {2, -1, 15};

// --------- apply*_impl --------------
Function fn_532;
Value *arityImpl_537(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
incRef((Value *)(Value *)&protoFn_1);
varArgs2 = (List *)listCons((Value *)(Value *)&protoFn_1, varArgs2);
Value *rslt3 = arityImpl_401(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};


// --------- apply*_impl main body --------------
Function fn_532 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_537}}};

Value *protoImpl_538(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_531 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_538}}};


// --------- invoke_impl --------------
Function fn_534;

// --------- flatten_impl --------------
Function fn_541;
Value *arityImpl_562(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val1);
return(val1);
};

Value *protoImpl_563(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_540 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_563}}};


// --------- flat-map_impl --------------
Function fn_543;
Value *arityImpl_564(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt6;
if((arg1)->type != FunctionType) {
rslt6 = protoFnImpl_11(empty_list, arg1, val2);
} else {
FnArity *arity3 = findFnArity(arg1, 1);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
rslt6 = fn5(arity3->closures, val2);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(val2);
varArgs4 = (List *)listCons(val2, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
return(rslt6);
};

Value *protoImpl_565(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_542 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_565}}};


// --------- wrap_impl --------------
Function fn_545;
Value *arityImpl_566(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_530(empty_list, var_470, arg1);
return(rslt2);
};


// --------- wrap_impl main body --------------
Function fn_545 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_566}}};

Value *protoImpl_567(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_544 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_567}}};


// --------- apply*_impl --------------
Function fn_547;
Value *arityImpl_568(List *closures, Value *arg0, Value *arg1) {
Value * val14  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)(Value *)&reified_522);
varArgs2 = (List *)listCons((Value *)(Value *)&reified_522, varArgs2);
incRef((Value *)(Value *)&fn_460);
varArgs2 = (List *)listCons((Value *)(Value *)&fn_460, varArgs2);
Value *rslt3 = arityImpl_466(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_180(empty_list, arg1, rslt3);
Value *rslt5 = protoFnImpl_27(empty_list, rslt4);
Value *cond6;
Value *cond7;

if (isTrue((Value *)&trueVal)) {
dec_and_free((Value *)&trueVal);
Value *cond8;
Value *rslt9 = protoFnImpl_222(empty_list, rslt5);
Value *rslt10 = protoFnImpl_200(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_76);
cond8 = var_76;
} else {
dec_and_free(rslt10);
incRef(var_75);
cond8 = var_75;
}
incRef(cond8);
cond7 = cond8;
dec_and_free(cond8);
} else {
dec_and_free((Value *)&trueVal);
incRef(var_76);
cond7 = var_76;
}

if (isTrue(cond7)) {
dec_and_free(cond7);
List *arg13 = (List *)rslt5;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *rslt15 = protoFnImpl_337(empty_list, arg1, (Value *)&protoFn_525);
List *varArgs16 = empty_list;
incRef((Value *)rslt15);
varArgs16 = (List *)listCons((Value *)rslt15, varArgs16);
Value *rslt17 = arityImpl_186(empty_list, (Value *)varArgs16);
dec_and_free((Value *)varArgs16);
Value *rslt18 = protoFnImpl_316(empty_list, val14, rslt17);
Value *rslt19 = protoFnImpl_530(empty_list, var_470, rslt18);
incRef(rslt19);
cond6 = rslt19;
dec_and_free(rslt15);
dec_and_free(rslt19);
dec_and_free(rslt18);
dec_and_free(rslt17);
} else {
dec_and_free(cond7);
incRef((Value *)&reified_522);
cond6 = (Value *)&reified_522;
}
incRef(cond6);
dec_and_free(cond6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(cond6);
};

Value *protoImpl_572(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_546 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_572}}};


// --------- zero_impl --------------
Function fn_549;
Value *arityImpl_573(List *closures, Value *arg0) {
incRef((Value *)&reified_522);
return((Value *)&reified_522);
};


// --------- zero_impl main body --------------
Function fn_549 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_573}}};

Value *protoImpl_574(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_548 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_574}}};


// --------- comp*_impl --------------
Function fn_551;
Value *arityImpl_575(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- comp*_impl main body --------------
Function fn_551 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_575}}};

Value *protoImpl_576(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_550 = {FunctionType, -1, "comp*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_576}}};


// --------- string-list_impl --------------
Function fn_553;
Value *arityImpl_577(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_45);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_45, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = protoFnImpl_527(empty_list, arg0);
Value *rslt4 = protoFnImpl_239(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_46, varArgs5);
Value *rslt6 = arityImpl_186(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
Value *rslt8 = arityImpl_186(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = protoFnImpl_396(empty_list, rslt2, rslt8);
incRef(rslt9);
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt9);
};


// --------- string-list_impl main body --------------
Function fn_553 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_577}}};

Value *protoImpl_578(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_552 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_578}}};


// --------- map_impl --------------
Function fn_555;
Value *arityImpl_579(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt6;
if((arg1)->type != FunctionType) {
rslt6 = protoFnImpl_11(empty_list, arg1, val2);
} else {
FnArity *arity3 = findFnArity(arg1, 1);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
rslt6 = fn5(arity3->closures, val2);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(val2);
varArgs4 = (List *)listCons(val2, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
Value *rslt7 = protoFnImpl_530(empty_list, var_470, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt7);
return(rslt7);
};

Value *protoImpl_580(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_554 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_580}}};


// --------- type-args_impl --------------
Function fn_557;
Value *arityImpl_581(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)val1);
varArgs2 = (List *)listCons((Value *)val1, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};

Value *protoImpl_582(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_556 = {FunctionType, -1, "type-args", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_582}}};


// --------- type-name_impl --------------
Function fn_559;
Value *arityImpl_583(List *closures, Value *arg0) {
incRef((Value *)&_str_47);
return((Value *)&_str_47);
};


// --------- type-name_impl main body --------------
Function fn_559 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_583}}};

Value *protoImpl_584(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_558 = {FunctionType, -1, "type-name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_584}}};


// --------- .v_impl --------------
Function fn_561;
Value *arityImpl_585(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val1);
return(val1);
};

Value *protoImpl_586(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_560 = {FunctionType, -1, ".v", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_586}}};

Value *arityImpl_539(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_562;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_541 = malloc_function(1);
fn_541->type = FunctionType;
fn_541->name = "flatten_impl";
fn_541->arityCount = 1;
fn_541->arities[0] = arity_2;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_564;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_543 = malloc_function(1);
fn_543->type = FunctionType;
fn_543->name = "flat-map_impl";
fn_543->arityCount = 1;
fn_543->arities[0] = arity_3;
FnArity *arity_5 = malloc_fnArity();
arity_5->type = FnArityType;
arity_5->count = 2;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_568;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_547 = malloc_function(1);
fn_547->type = FunctionType;
fn_547->name = "apply*_impl";
fn_547->arityCount = 1;
fn_547->arities[0] = arity_5;
FnArity *arity_9 = malloc_fnArity();
arity_9->type = FnArityType;
arity_9->count = 2;
arity_9->closures = empty_list;
arity_9->variadic = 0;
arity_9->fn = arityImpl_579;
incRef((Value *)arg1);
arity_9->closures = listCons((Value *)arg1, (List *)arity_9->closures);
Function *fn_555 = malloc_function(1);
fn_555->type = FunctionType;
fn_555->name = "map_impl";
fn_555->arityCount = 1;
fn_555->arities[0] = arity_9;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = FnArityType;
arity_10->count = 1;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_581;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_557 = malloc_function(1);
fn_557->type = FunctionType;
fn_557->name = "type-args_impl";
fn_557->arityCount = 1;
fn_557->arities[0] = arity_10;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = FnArityType;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_585;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_561 = malloc_function(1);
fn_561->type = FunctionType;
fn_561->name = ".v_impl";
fn_561->arityCount = 1;
fn_561->arities[0] = arity_12;
Value *reified_13 = (Value *)malloc_reified(11);
((ReifiedVal *)reified_13)->type = 15;
((ReifiedVal *)reified_13)->implCount = 11;
((ReifiedVal *)reified_13)->impls[0] = (Value *)fn_541;
incRef((Value *)fn_541);
((ReifiedVal *)reified_13)->impls[1] = (Value *)fn_543;
incRef((Value *)fn_543);
((ReifiedVal *)reified_13)->impls[2] = (Value *)&fn_545;
incRef((Value *)&fn_545);
((ReifiedVal *)reified_13)->impls[3] = (Value *)fn_547;
incRef((Value *)fn_547);
((ReifiedVal *)reified_13)->impls[4] = (Value *)&fn_549;
incRef((Value *)&fn_549);
((ReifiedVal *)reified_13)->impls[5] = (Value *)&fn_551;
incRef((Value *)&fn_551);
((ReifiedVal *)reified_13)->impls[6] = (Value *)&fn_553;
incRef((Value *)&fn_553);
((ReifiedVal *)reified_13)->impls[7] = (Value *)fn_555;
incRef((Value *)fn_555);
((ReifiedVal *)reified_13)->impls[8] = (Value *)fn_557;
incRef((Value *)fn_557);
((ReifiedVal *)reified_13)->impls[9] = (Value *)&fn_559;
incRef((Value *)&fn_559);
((ReifiedVal *)reified_13)->impls[10] = (Value *)fn_561;
incRef((Value *)fn_561);
incRef(reified_13);
dec_and_free((Value *)fn_541);
dec_and_free((Value *)fn_543);
dec_and_free(reified_13);
dec_and_free((Value *)fn_557);
dec_and_free((Value *)fn_555);
dec_and_free((Value *)fn_547);
dec_and_free((Value *)fn_561);
return(reified_13);
};


// --------- invoke_impl main body --------------
Function fn_534 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_539}}};

Value *protoFnImpl_530(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_533 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoFnImpl_530}}};


// --------- instance?_impl --------------
Function fn_536;
Value *arityImpl_587(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_99(empty_list, arg1);
Value *rslt3 = arityImpl_462(empty_list, (Value *)&_num_14, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- instance?_impl main body --------------
Function fn_536 = {FunctionType, -1, "instance?_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_587}}};

Value *protoImpl_588(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_535 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_588}}};

ReifiedVal reified_589 = {14, -1, 3, {(Value *)&fn_532, (Value *)&fn_534, (Value *)&fn_536}};
Value *var_470 = (Value *)&reified_589;

// --------- zero_impl --------------
Function fn_591;
Value *arityImpl_596(List *closures, Value *arg0) {
incRef((Value *)&reified_522);
return((Value *)&reified_522);
};


// --------- zero_impl main body --------------
Function fn_591 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_596}}};

Value *protoImpl_597(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_590 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_597}}};


// --------- invoke_impl --------------
Function fn_593;
Value *arityImpl_598(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_530(empty_list, var_470, arg1);
return(rslt2);
};


// --------- invoke_impl main body --------------
Function fn_593 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_598}}};

Value *protoImpl_599(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_592 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_599}}};


// --------- instance?_impl --------------
Function fn_595;
Value *arityImpl_600(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoImpl_588(empty_list, var_470, arg1);
return(rslt2);
};


// --------- instance?_impl main body --------------
Function fn_595 = {FunctionType, -1, "instance?_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_600}}};

Value *protoImpl_601(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_594 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_601}}};

ReifiedVal reified_602 = {16, -1, 3, {(Value *)&fn_591, (Value *)&fn_593, (Value *)&fn_595}};

// --------- m= --------------
Function fn_605;
Value *arityImpl_606(List *closures, Value *arg0) {
Value *rslt1 = protoImpl_599(empty_list, (Value *)&reified_602, arg0);
return(rslt1);
};

Value *arityImpl_607(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt3 = protoFnImpl_245(empty_list, arg0, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
Value *rslt4 = protoImpl_599(empty_list, (Value *)&reified_602, arg0);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
} else {
dec_and_free(rslt3);
incRef((Value *)&reified_522);
cond2 = (Value *)&reified_522;
}
return(cond2);
};


// --------- recur --------------
Function fn_612;

// --------- anon --------------
Function fn_614;

// --------- anon --------------
Function fn_616;
Value *arityImpl_617(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt3 = protoFnImpl_306(empty_list, val1, val2);
return(rslt3);
};

Value *arityImpl_615(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val7  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val8  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt5;
FnArity *arity2 = findFnArity((Value *)&fn_612, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, val1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(val1);
varArgs3 = (List *)listCons(val1, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_612)->name);
  abort();
}
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_617;
incRef((Value *)val7);
arity_6->closures = listCons((Value *)val7, (List *)arity_6->closures);
incRef((Value *)val8);
arity_6->closures = listCons((Value *)val8, (List *)arity_6->closures);
Function *fn_616 = malloc_function(1);
fn_616->type = FunctionType;
fn_616->name = "anon";
fn_616->arityCount = 1;
fn_616->arities[0] = arity_6;
Value *rslt9 = protoFnImpl_275(empty_list, rslt5, (Value *)fn_616);
incRef(rslt9);
dec_and_free((Value *)fn_616);
dec_and_free(rslt9);
dec_and_free(rslt5);
return(rslt9);
};

Value *arityImpl_613(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val8  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt6;
FnArity *arity3 = findFnArity((Value *)&fn_605, 2);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType2 *fn5 = (FnType2 *)arity3->fn;
rslt6 = fn5(arity3->closures, val2, arg0);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(arg0);
varArgs4 = (List *)listCons(arg0, varArgs4);
incRef(val2);
varArgs4 = (List *)listCons(val2, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_605)->name);
  abort();
}
FnArity *arity_7 = malloc_fnArity();
arity_7->type = FnArityType;
arity_7->count = 1;
arity_7->closures = empty_list;
arity_7->variadic = 0;
arity_7->fn = arityImpl_615;
incRef((Value *)rslt6);
arity_7->closures = listCons((Value *)rslt6, (List *)arity_7->closures);
incRef((Value *)val8);
arity_7->closures = listCons((Value *)val8, (List *)arity_7->closures);
incRef((Value *)arg1);
arity_7->closures = listCons((Value *)arg1, (List *)arity_7->closures);
Function *fn_614 = malloc_function(1);
fn_614->type = FunctionType;
fn_614->name = "anon";
fn_614->arityCount = 1;
fn_614->arities[0] = arity_7;
Value *rslt9 = protoFnImpl_275(empty_list, rslt6, (Value *)fn_614);
incRef(rslt9);
dec_and_free(rslt6);
dec_and_free((Value *)fn_614);
dec_and_free(rslt9);
return(rslt9);
};
Value *arityImpl_608(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond5;

if (isTrue((Value *)&trueVal)) {
dec_and_free((Value *)&trueVal);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond5 = cond6;
dec_and_free(cond6);
} else {
dec_and_free((Value *)&trueVal);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg11 = (List *)rslt2;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = FnArityType;
arity_12->count = 2;
arity_12->closures = empty_list;
arity_12->variadic = 1;
arity_12->fn = arityImpl_613;
incRef((Value *)arg0);
arity_12->closures = listCons((Value *)arg0, (List *)arity_12->closures);
incRef((Value *)arg0);
arity_12->closures = listCons((Value *)arg0, (List *)arity_12->closures);
Function *fn_612 = malloc_function(1);
fn_612->type = FunctionType;
fn_612->name = "recur";
fn_612->arityCount = 1;
fn_612->arities[0] = arity_12;
Value *rslt16;
FnArity *arity13 = findFnArity((Value *)fn_612, 1);
if(arity13 != (FnArity *)0 && !arity13->variadic) {
FnType1 *fn15 = (FnType1 *)arity13->fn;
rslt16 = fn15(arity13->closures, arg1);
} else if(arity13 != (FnArity *)0 && arity13->variadic) {
FnType1 *fn15 = (FnType1 *)arity13->fn;
List *varArgs14 = empty_list;
incRef(arg1);
varArgs14 = (List *)listCons(arg1, varArgs14);
rslt16 = fn15(arity13->closures, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)fn_612)->name);
  abort();
}
incRef(rslt16);
cond3 = rslt16;
dec_and_free(rslt16);
dec_and_free((Value *)fn_612);
} else {
dec_and_free(cond5);
Value *rslt4 = protoImpl_599(empty_list, (Value *)&reified_602, arg0);
incRef(rslt4);
cond3 = rslt4;
dec_and_free(rslt4);
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};

// --------- m= main body --------------
Function fn_605 = {FunctionType, -1, "m=", 3, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_606}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_607}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_608}}};


// --------- some --------------
Function fn_619;
Value *arityImpl_620(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_337(empty_list, arg0, arg1);
Value *rslt3 = protoImpl_509(empty_list, (Value *)&reified_522, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- some main body --------------
Function fn_619 = {FunctionType, -1, "some", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_620}}};


// --------- < --------------
Function fn_622;
Value *arityImpl_623(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_200(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_624(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;
Value *rslt6 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef((Value *)&_num_1);
cond2 = (Value *)&_num_1;
} else {
dec_and_free(rslt6);
Value *rslt7 = arityImpl_141(empty_list, arg1);
Value *rslt8 = protoFnImpl_200(empty_list, arg0, rslt7);
Value *rslt9 = arityImpl_189(empty_list, rslt8);
dec_and_free(rslt8);
dec_and_free(rslt7);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt9);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_186(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_316(empty_list, (Value *)&fn_622, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
}
return(cond2);
};

// --------- < main body --------------
Function fn_622 = {FunctionType, -1, "<", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_623}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_624}}};


// --------- m< --------------
Function fn_626;
Value *arityImpl_627(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt3 = protoFnImpl_200(empty_list, arg0, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
Value *rslt4 = protoImpl_599(empty_list, (Value *)&reified_602, arg0);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
} else {
dec_and_free(rslt3);
incRef((Value *)&reified_522);
cond2 = (Value *)&reified_522;
}
return(cond2);
};

Value *arityImpl_628(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;
Value *rslt6 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *rslt7 = protoImpl_599(empty_list, (Value *)&reified_602, arg0);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt7);
} else {
dec_and_free(rslt6);
Value *rslt8 = arityImpl_141(empty_list, arg1);
Value *rslt9 = protoFnImpl_200(empty_list, arg0, rslt8);
Value *rslt10 = arityImpl_189(empty_list, rslt9);
dec_and_free(rslt8);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef((Value *)&reified_522);
cond2 = (Value *)&reified_522;
} else {
dec_and_free(rslt10);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_186(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_316(empty_list, (Value *)&fn_626, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
}
return(cond2);
};

// --------- m< main body --------------
Function fn_626 = {FunctionType, -1, "m<", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_627}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_628}}};


// --------- list** --------------
Function fn_630;
Value *arityImpl_631(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond4 = cond6;
dec_and_free(cond6);
} else {
dec_and_free(rslt5);
incRef(var_76);
cond4 = var_76;
}

if (isTrue(cond4)) {
dec_and_free(cond4);
List *arg11 = (List *)rslt2;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
Value *rslt12 = arityImpl_631(closures, arg9, arg10);
Value *rslt13 = arityImpl_132(empty_list, arg0, rslt12);
incRef(rslt13);
cond3 = rslt13;
dec_and_free(rslt13);
dec_and_free(rslt12);
} else {
dec_and_free(cond4);
incRef(arg0);
cond3 = arg0;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- list** main body --------------
Function fn_630 = {FunctionType, -1, "list**", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_631}}};


// --------- list* --------------
Function fn_636;
Value *arityImpl_637(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = arityImpl_631(empty_list, arg0, arg1);
return(rslt2);
};

// --------- list* main body --------------
Function fn_636 = {FunctionType, -1, "list*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_637}}};


// --------- identity --------------
Function fn_639;
Value *arityImpl_640(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_639 = {FunctionType, -1, "identity", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_640}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_48 = {1, -1, 5,"<Fn: "};

// --------- apply*_impl --------------
Function fn_642;
Value *arityImpl_646(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt8 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
Value *rslt12;
if((arg0)->type != FunctionType) {
rslt12 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity9 = findFnArity(arg0, 0);
if(arity9 != (FnArity *)0 && !arity9->variadic) {
FnType0 *fn11 = (FnType0 *)arity9->fn;
rslt12 = fn11(arity9->closures);
} else if(arity9 != (FnArity *)0 && arity9->variadic) {
FnType1 *fn11 = (FnType1 *)arity9->fn;
List *varArgs10 = empty_list;
rslt12 = fn11(arity9->closures, (Value *)varArgs10);
dec_and_free((Value *)varArgs10);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
incRef(rslt12);
cond2 = rslt12;
dec_and_free(rslt12);
} else {
dec_and_free(rslt8);
List *arg5 = (List *)arg1;
Value *arg3 = arg5->head;
if (arg5->tail) arg5->tail->len = arg5->len - 1;
arg5 = arg5->tail;
Value *arg4 = (Value *) arg5;
Value *rslt6 = arityImpl_631(empty_list, arg3, arg4);
Value *rslt7 = arityImpl_174(empty_list, arg0, rslt6);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
}
return(cond2);
};


// --------- apply*_impl main body --------------
Function fn_642 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_646}}};


// --------- zero_impl --------------
Function fn_643;
Value *arityImpl_647(List *closures, Value *arg0) {
incRef((Value *)&fn_639);
return((Value *)&fn_639);
};


// --------- zero_impl main body --------------
Function fn_643 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_647}}};


// --------- comp*_impl --------------
Function fn_644;

// --------- anon --------------
Function fn_649;

// --------- anon --------------
Function fn_651;
Value *arityImpl_652(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((arg1)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, arg1, arg0);
} else {
FnArity *arity2 = findFnArity(arg1, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, arg0);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
return(rslt5);
};


// --------- anon main body --------------
Function fn_651 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_652}}};

Value *arityImpl_650(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
Value *rslt4 = arityImpl_186(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_316(empty_list, val2, rslt4);
Value *rslt7 = protoFnImpl_230(empty_list, val1, rslt5, (Value *)&fn_651);
incRef(rslt7);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt7);
};
Value *arityImpl_648(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 2;
arity_2->closures = empty_list;
arity_2->variadic = 1;
arity_2->fn = arityImpl_650;
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_649 = malloc_function(1);
fn_649->type = FunctionType;
fn_649->name = "anon";
fn_649->arityCount = 1;
fn_649->arities[0] = arity_2;
return((Value *)fn_649);
};


// --------- comp*_impl main body --------------
Function fn_644 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_648}}};


// --------- string-list_impl --------------
Function fn_645;
Value *arityImpl_653(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_147(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_46, varArgs2);
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)(Value *)&_str_48);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_48, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_645 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_653}}};


// --------- list-concat --------------
Function fn_654;
Value *arityImpl_655(List *closures, Value *arg0) {
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
    List *tail = empty_list;
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
Function fn_654 = {FunctionType, -1, "list-concat", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_655}}};


// --------- list=* --------------
Function fn_657;
Value *arityImpl_658(List *closures, Value *arg2, Value *arg6) {
List *arg3 = (List *)arg2;
Value *arg0 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *arg1 = (Value *) arg3;
List *arg7 = (List *)arg6;
Value *arg4 = arg7->head;
if (arg7->tail) arg7->tail->len = arg7->len - 1;
arg7 = arg7->tail;
Value *arg5 = (Value *) arg7;
Value *cond8;
Value *rslt9 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef((Value *)&_num_1);
cond8 = (Value *)&_num_1;
} else {
dec_and_free(rslt9);
Value *rslt10 = protoFnImpl_245(empty_list, arg0, arg4);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
Value *rslt11 = arityImpl_658(closures, arg1, arg5);
incRef(rslt11);
cond8 = rslt11;
dec_and_free(rslt11);
} else {
dec_and_free(rslt10);
incRef((Value *)&_num_13);
cond8 = (Value *)&_num_13;
}
}
return(cond8);
};


// --------- list=* main body --------------
Function fn_657 = {FunctionType, -1, "list=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_658}}};


// --------- reduce-list --------------
Function fn_660;
Value *arityImpl_661(List *closures, Value *arg2, Value *arg4, Value *arg5) {
List *arg3 = (List *)arg2;
Value *arg0 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *arg1 = (Value *) arg3;
Value *rslt6 = protoFnImpl_27(empty_list, arg1);
Value *cond7;
Value *cond12;

if (isTrue((Value *)&trueVal)) {
dec_and_free((Value *)&trueVal);
Value *cond13;
Value *rslt14 = protoFnImpl_222(empty_list, rslt6);
Value *rslt15 = protoFnImpl_200(empty_list, rslt14, (Value *)&_num_1);
dec_and_free(rslt14);

if (isTrue(rslt15)) {
dec_and_free(rslt15);
incRef(var_76);
cond13 = var_76;
} else {
dec_and_free(rslt15);
incRef(var_75);
cond13 = var_75;
}
incRef(cond13);
cond12 = cond13;
dec_and_free(cond13);
} else {
dec_and_free((Value *)&trueVal);
incRef(var_76);
cond12 = var_76;
}

if (isTrue(cond12)) {
dec_and_free(cond12);
List *arg18 = (List *)rslt6;
Value *arg16 = arg18->head;
if (arg18->tail) arg18->tail->len = arg18->len - 1;
arg18 = arg18->tail;
Value *arg17 = (Value *) arg18;
Value *rslt22;
if((arg5)->type != FunctionType) {
rslt22 = protoFnImpl_13(empty_list, arg5, arg4, arg0);
} else {
FnArity *arity19 = findFnArity(arg5, 2);
if(arity19 != (FnArity *)0 && !arity19->variadic) {
FnType2 *fn21 = (FnType2 *)arity19->fn;
rslt22 = fn21(arity19->closures, arg4, arg0);
} else if(arity19 != (FnArity *)0 && arity19->variadic) {
FnType1 *fn21 = (FnType1 *)arity19->fn;
List *varArgs20 = empty_list;
incRef(arg0);
varArgs20 = (List *)listCons(arg0, varArgs20);
incRef(arg4);
varArgs20 = (List *)listCons(arg4, varArgs20);
rslt22 = fn21(arity19->closures, (Value *)varArgs20);
dec_and_free((Value *)varArgs20);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg5)->name);
  abort();
}
}
Value *rslt23 = arityImpl_661(closures, arg1, rslt22, arg5);
incRef(rslt23);
cond7 = rslt23;
dec_and_free(rslt22);
dec_and_free(rslt23);
} else {
dec_and_free(cond12);
Value *rslt11;
if((arg5)->type != FunctionType) {
rslt11 = protoFnImpl_13(empty_list, arg5, arg4, arg0);
} else {
FnArity *arity8 = findFnArity(arg5, 2);
if(arity8 != (FnArity *)0 && !arity8->variadic) {
FnType2 *fn10 = (FnType2 *)arity8->fn;
rslt11 = fn10(arity8->closures, arg4, arg0);
} else if(arity8 != (FnArity *)0 && arity8->variadic) {
FnType1 *fn10 = (FnType1 *)arity8->fn;
List *varArgs9 = empty_list;
incRef(arg0);
varArgs9 = (List *)listCons(arg0, varArgs9);
incRef(arg4);
varArgs9 = (List *)listCons(arg4, varArgs9);
rslt11 = fn10(arity8->closures, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg5)->name);
  abort();
}
}
incRef(rslt11);
cond7 = rslt11;
dec_and_free(rslt11);
}
incRef(cond7);
dec_and_free(rslt6);
dec_and_free(cond7);
return(cond7);
};


// --------- reduce-list main body --------------
Function fn_660 = {FunctionType, -1, "reduce-list", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_661}}};


// --------- traverse_impl --------------
Function fn_666;
Value *arityImpl_685(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_337(empty_list, arg0, arg1);
Value *rslt3 = protoFnImpl_27(empty_list, rslt2);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt2);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *cond7;
Value *rslt8 = protoFnImpl_222(empty_list, rslt3);
Value *rslt9 = protoFnImpl_200(empty_list, rslt8, (Value *)&_num_1);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(var_76);
cond7 = var_76;
} else {
dec_and_free(rslt9);
incRef(var_75);
cond7 = var_75;
}
incRef(cond7);
cond5 = cond7;
dec_and_free(cond7);
} else {
dec_and_free(rslt6);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg12 = (List *)rslt3;
Value *arg10 = arg12->head;
if (arg12->tail) arg12->tail->len = arg12->len - 1;
arg12 = arg12->tail;
Value *arg11 = (Value *) arg12;
Value *rslt13 = protoFnImpl_306(empty_list, arg10, (Value *)&fn_185);
Value *rslt14 = arityImpl_132(empty_list, arg10, arg11);
Value *rslt15 = protoFnImpl_316(empty_list, rslt13, rslt14);
incRef(rslt15);
cond4 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(rslt13);
} else {
dec_and_free(cond5);
incRef((Value *)&reified_522);
cond4 = (Value *)&reified_522;
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(cond4);
};


// --------- traverse_impl main body --------------
Function fn_666 = {FunctionType, -1, "traverse_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_685}}};


// --------- empty?_impl --------------
Function fn_667;
Value *arityImpl_689(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_138(empty_list, arg0);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_667 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_689}}};


// --------- empty_impl --------------
Function fn_668;
Value *arityImpl_690(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- empty_impl main body --------------
Function fn_668 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_690}}};


// --------- conj_impl --------------
Function fn_669;
Value *arityImpl_691(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_132(empty_list, arg1, arg0);
return(rslt2);
};


// --------- conj_impl main body --------------
Function fn_669 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_691}}};


// --------- count_impl --------------
Function fn_670;
Value *arityImpl_692(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_135(empty_list, arg0);
return(rslt1);
};


// --------- count_impl main body --------------
Function fn_670 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_692}}};


// --------- reduce_impl --------------
Function fn_671;
Value *arityImpl_693(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_27(empty_list, arg0);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *cond7;
Value *rslt8 = protoFnImpl_222(empty_list, rslt3);
Value *rslt9 = protoFnImpl_200(empty_list, rslt8, (Value *)&_num_1);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(var_76);
cond7 = var_76;
} else {
dec_and_free(rslt9);
incRef(var_75);
cond7 = var_75;
}
incRef(cond7);
cond5 = cond7;
dec_and_free(cond7);
} else {
dec_and_free(rslt6);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg12 = (List *)rslt3;
Value *arg10 = arg12->head;
if (arg12->tail) arg12->tail->len = arg12->len - 1;
arg12 = arg12->tail;
Value *arg11 = (Value *) arg12;
Value *rslt13 = arityImpl_661(empty_list, arg0, arg1, arg2);
incRef(rslt13);
cond4 = rslt13;
dec_and_free(rslt13);
} else {
dec_and_free(cond5);
incRef(arg1);
cond4 = arg1;
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
return(cond4);
};


// --------- reduce_impl main body --------------
Function fn_671 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_693}}};


// --------- crush_impl --------------
Function fn_672;

// --------- anon --------------
Function fn_698;
Value *arityImpl_699(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt6;
if((val2)->type != FunctionType) {
rslt6 = protoFnImpl_11(empty_list, val2, arg1);
} else {
FnArity *arity3 = findFnArity(val2, 1);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
rslt6 = fn5(arity3->closures, arg1);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(arg1);
varArgs4 = (List *)listCons(arg1, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val2)->name);
  abort();
}
}
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
Value *rslt8 = arityImpl_186(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = protoFnImpl_396(empty_list, arg0, rslt8);
incRef(rslt9);
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt9);
return(rslt9);
};

Value *arityImpl_697(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_144(empty_list, arg0);
Value *rslt3 = arityImpl_141(empty_list, arg0);
Value *rslt7;
if((arg1)->type != FunctionType) {
rslt7 = protoFnImpl_11(empty_list, arg1, rslt3);
} else {
FnArity *arity4 = findFnArity(arg1, 1);
if(arity4 != (FnArity *)0 && !arity4->variadic) {
FnType1 *fn6 = (FnType1 *)arity4->fn;
rslt7 = fn6(arity4->closures, rslt3);
} else if(arity4 != (FnArity *)0 && arity4->variadic) {
FnType1 *fn6 = (FnType1 *)arity4->fn;
List *varArgs5 = empty_list;
incRef(rslt3);
varArgs5 = (List *)listCons(rslt3, varArgs5);
rslt7 = fn6(arity4->closures, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
FnArity *arity_8 = malloc_fnArity();
arity_8->type = FnArityType;
arity_8->count = 2;
arity_8->closures = empty_list;
arity_8->variadic = 0;
arity_8->fn = arityImpl_699;
incRef((Value *)arg1);
arity_8->closures = listCons((Value *)arg1, (List *)arity_8->closures);
Function *fn_698 = malloc_function(1);
fn_698->type = FunctionType;
fn_698->name = "anon";
fn_698->arityCount = 1;
fn_698->arities[0] = arity_8;
Value *rslt9 = arityImpl_693(empty_list, rslt2, rslt7, (Value *)fn_698);
incRef(rslt9);
dec_and_free((Value *)fn_698);
dec_and_free(rslt9);
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt9);
};


// --------- crush_impl main body --------------
Function fn_672 = {FunctionType, -1, "crush_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_697}}};


// --------- flat-map_impl --------------
Function fn_673;
Value *arityImpl_700(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_337(empty_list, arg0, arg1);
Value *rslt3 = protoFnImpl_27(empty_list, rslt2);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt2);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *cond7;
Value *rslt8 = protoFnImpl_222(empty_list, rslt3);
Value *rslt9 = protoFnImpl_200(empty_list, rslt8, (Value *)&_num_1);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(var_76);
cond7 = var_76;
} else {
dec_and_free(rslt9);
incRef(var_75);
cond7 = var_75;
}
incRef(cond7);
cond5 = cond7;
dec_and_free(cond7);
} else {
dec_and_free(rslt6);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg12 = (List *)rslt3;
Value *arg10 = arg12->head;
if (arg12->tail) arg12->tail->len = arg12->len - 1;
arg12 = arg12->tail;
Value *arg11 = (Value *) arg12;
Value *rslt13 = protoFnImpl_396(empty_list, arg10, arg11);
incRef(rslt13);
cond4 = rslt13;
dec_and_free(rslt13);
} else {
dec_and_free(cond5);
incRef(var_129);
cond4 = var_129;
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(cond4);
};


// --------- flat-map_impl main body --------------
Function fn_673 = {FunctionType, -1, "flat-map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_700}}};


// --------- wrap_impl --------------
Function fn_674;
Value *arityImpl_704(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_674 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_704}}};


// --------- zero_impl --------------
Function fn_675;
Value *arityImpl_705(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- zero_impl main body --------------
Function fn_675 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_705}}};


// --------- comp*_impl --------------
Function fn_676;
Value *arityImpl_706(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_655(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_676 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_706}}};


// --------- =*_impl --------------
Function fn_677;
Value *arityImpl_707(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt4 = arityImpl_99(empty_list, arg0);
Value *rslt5 = arityImpl_99(empty_list, arg1);
Value *rslt6 = arityImpl_112(empty_list, rslt4, rslt5);
Value *rslt7 = arityImpl_189(empty_list, rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt7);
Value *rslt8 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
Value *rslt9 = arityImpl_138(empty_list, arg1);
incRef(rslt9);
cond2 = rslt9;
dec_and_free(rslt9);
} else {
dec_and_free(rslt8);
Value *rslt10 = protoFnImpl_222(empty_list, arg0);
Value *rslt11 = protoFnImpl_222(empty_list, arg1);
Value *rslt12 = arityImpl_112(empty_list, rslt10, rslt11);
Value *rslt13 = arityImpl_189(empty_list, rslt12);
dec_and_free(rslt10);
dec_and_free(rslt11);
dec_and_free(rslt12);

if (isTrue(rslt13)) {
dec_and_free(rslt13);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt13);
Value *rslt3 = arityImpl_658(empty_list, arg0, arg1);
incRef(rslt3);
cond2 = rslt3;
dec_and_free(rslt3);
}
}
}
return(cond2);
};


// --------- =*_impl main body --------------
Function fn_677 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_707}}};


// --------- seq?_impl --------------
Function fn_678;
Value *arityImpl_708(List *closures, Value *arg0) {
incRef(var_75);
return(var_75);
};


// --------- seq?_impl main body --------------
Function fn_678 = {FunctionType, -1, "seq?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_708}}};


// --------- seq_impl --------------
Function fn_679;
Value *arityImpl_709(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_679 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_709}}};


// --------- m-first_impl --------------
Function fn_680;
Value *arityImpl_710(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_27(empty_list, arg0);
Value *cond2;
Value *cond3;
Value *rslt4 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
Value *cond5;
Value *rslt6 = protoFnImpl_222(empty_list, rslt1);
Value *rslt7 = protoFnImpl_200(empty_list, rslt6, (Value *)&_num_1);
dec_and_free(rslt6);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(var_76);
cond5 = var_76;
} else {
dec_and_free(rslt7);
incRef(var_75);
cond5 = var_75;
}
incRef(cond5);
cond3 = cond5;
dec_and_free(cond5);
} else {
dec_and_free(rslt4);
incRef(var_76);
cond3 = var_76;
}

if (isTrue(cond3)) {
dec_and_free(cond3);
List *arg10 = (List *)rslt1;
Value *arg8 = arg10->head;
if (arg10->tail) arg10->tail->len = arg10->len - 1;
arg10 = arg10->tail;
Value *arg9 = (Value *) arg10;
Value *rslt11 = protoImpl_599(empty_list, (Value *)&reified_602, arg8);
incRef(rslt11);
cond2 = rslt11;
dec_and_free(rslt11);
} else {
dec_and_free(cond3);
incRef((Value *)&reified_522);
cond2 = (Value *)&reified_522;
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};


// --------- m-first_impl main body --------------
Function fn_680 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_710}}};


// --------- first_impl --------------
Function fn_681;
Value *arityImpl_714(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_141(empty_list, arg0);
return(rslt1);
};


// --------- first_impl main body --------------
Function fn_681 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_714}}};


// --------- rest_impl --------------
Function fn_682;
Value *arityImpl_715(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_144(empty_list, arg0);
return(rslt1);
};


// --------- rest_impl main body --------------
Function fn_682 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_715}}};


// --------- map_impl --------------
Function fn_683;
Value *arityImpl_716(List *closures, Value *arg0, Value *arg1) {
List *l = (List *)arg0;
      if (l->len == 0)
        return((Value *)empty_list);
      else {
        List *head = empty_list;
        List *tail = empty_list;
        for(Value *x = l->head; x != (Value *)0; l = l->tail, x = l->head) {
          Value *y;
          if(arg1->type != 3) {
            y = protoFnImpl_11(empty_list, arg1, x);
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
              dec_and_free((Value *)varArgs3);
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
Function fn_683 = {FunctionType, -1, "map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_716}}};


// --------- type-args_impl --------------
Function fn_684;
Value *arityImpl_717(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- type-args_impl main body --------------
Function fn_684 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_717}}};


// --------- interpose --------------
Function fn_718;

// --------- anon --------------
Function fn_723;
Value *arityImpl_724(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
incRef((Value *)val1);
varArgs2 = (List *)listCons((Value *)val1, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};

Value *arityImpl_719(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg0);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond4 = cond6;
dec_and_free(cond6);
} else {
dec_and_free(rslt5);
incRef(var_76);
cond4 = var_76;
}

if (isTrue(cond4)) {
dec_and_free(cond4);
List *arg11 = (List *)rslt2;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = FnArityType;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_724;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_723 = malloc_function(1);
fn_723->type = FunctionType;
fn_723->name = "anon";
fn_723->arityCount = 1;
fn_723->arities[0] = arity_12;
Value *rslt13 = arityImpl_700(empty_list, arg10, (Value *)fn_723);
Value *rslt14 = arityImpl_132(empty_list, arg9, rslt13);
incRef(rslt14);
cond3 = rslt14;
dec_and_free((Value *)fn_723);
dec_and_free(rslt14);
dec_and_free(rslt13);
} else {
dec_and_free(cond4);
incRef(var_129);
cond3 = var_129;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- interpose main body --------------
Function fn_718 = {FunctionType, -1, "interpose", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_719}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_50 = {1, -1, 2,", "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_49 = {1, -1, 1,"("};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_51 = {1, -1, 1,")"};

// --------- string-list_impl --------------
Function fn_726;
Value *arityImpl_727(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_49);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_49, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_719(empty_list, arg0, (Value *)&_str_50);
Value *rslt4 = protoFnImpl_275(empty_list, rslt3, (Value *)&protoFn_236);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_51);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_51, varArgs5);
Value *rslt6 = arityImpl_186(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
incRef((Value *)rslt2);
varArgs7 = (List *)listCons((Value *)rslt2, varArgs7);
Value *rslt8 = arityImpl_186(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = arityImpl_655(empty_list, rslt8);
incRef(rslt9);
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt9);
};


// --------- string-list_impl main body --------------
Function fn_726 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_727}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_52 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_53 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_728;
Value *arityImpl_729(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_700(empty_list, arg0, (Value *)&protoFn_346);
Value *rslt2 = arityImpl_719(empty_list, rslt1, (Value *)&_str_52);
Value *rslt3 = protoFnImpl_337(empty_list, rslt2, (Value *)&fn_182);
Value *rslt4 = arityImpl_183(empty_list, (Value *)&_str_53);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- prn main body --------------
Function fn_728 = {FunctionType, -1, "prn", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_729}}};


// --------- print --------------
Function fn_731;
Value *arityImpl_732(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_719(empty_list, arg0, (Value *)&_str_52);
Value *rslt2 = protoFnImpl_275(empty_list, rslt1, (Value *)&protoFn_236);
Value *rslt3 = protoFnImpl_337(empty_list, rslt2, (Value *)&fn_182);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};

// --------- print main body --------------
Function fn_731 = {FunctionType, -1, "print", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_732}}};


// --------- println --------------
Function fn_734;
Value *arityImpl_735(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_719(empty_list, arg0, (Value *)&_str_52);
Value *rslt2 = protoFnImpl_275(empty_list, rslt1, (Value *)&protoFn_236);
Value *rslt3 = protoFnImpl_337(empty_list, rslt2, (Value *)&fn_182);
Value *rslt4 = arityImpl_183(empty_list, (Value *)&_str_53);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- println main body --------------
Function fn_734 = {FunctionType, -1, "println", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_735}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_54 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_738;
Value *arityImpl_739(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_168(empty_list, (Value *)&_str_54);
Value *rslt2 = arityImpl_719(empty_list, arg0, (Value *)&_str_52);
Value *rslt3 = protoFnImpl_275(empty_list, rslt2, (Value *)&protoFn_236);
Value *rslt4 = protoFnImpl_337(empty_list, rslt3, (Value *)&fn_167);
Value *rslt5 = arityImpl_168(empty_list, (Value *)&_str_53);
incRef(rslt5);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt5);
};

// --------- print-err main body --------------
Function fn_738 = {FunctionType, -1, "print-err", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_739}}};

Value *var_53 = (Value *)&fn_738;

// --------- inc --------------
Function fn_740;
Value *arityImpl_741(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_118(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- inc main body --------------
Function fn_740 = {FunctionType, -1, "inc", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_741}}};


// --------- + --------------
Function fn_743;
Value *arityImpl_744(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_745(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_118(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_746(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_693(empty_list, arg0, (Value *)&_num_13, (Value *)&fn_117);
return(rslt1);
};

// --------- + main body --------------
Function fn_743 = {FunctionType, -1, "+", 3, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_744}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_745}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_746}}};


// --------- * --------------
Function fn_748;
Value *arityImpl_749(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_750(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_124(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_751(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_693(empty_list, arg0, (Value *)&_num_13, (Value *)&fn_123);
return(rslt1);
};

// --------- * main body --------------
Function fn_748 = {FunctionType, -1, "*", 3, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_749}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_750}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_751}}};


// --------- dec --------------
Function fn_753;
Value *arityImpl_754(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_121(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- dec main body --------------
Function fn_753 = {FunctionType, -1, "dec", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_754}}};


// --------- - --------------
Function fn_756;
Value *arityImpl_757(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_758(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_759(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = arityImpl_693(empty_list, arg1, arg0, (Value *)&fn_120);
return(rslt2);
};

// --------- - main body --------------
Function fn_756 = {FunctionType, -1, "-", 3, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_757}, &(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_758}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_759}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_55 = {1, -1, 0,""};

// --------- sha1_impl --------------
Function fn_761;
Value *arityImpl_775(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
String *strVal = (String *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)strVal->buffer, strVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_761 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_775}}};


// --------- empty?_impl --------------
Function fn_762;
Value *arityImpl_776(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
Value *rslt2 = arityImpl_462(empty_list, (Value *)&_num_13, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- empty?_impl main body --------------
Function fn_762 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_776}}};


// --------- empty_impl --------------
Function fn_763;
Value *arityImpl_777(List *closures, Value *arg0) {
incRef((Value *)&_str_55);
return((Value *)&_str_55);
};


// --------- empty_impl main body --------------
Function fn_763 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_777}}};


// --------- count_impl --------------
Function fn_764;
Value *arityImpl_778(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
return(rslt1);
};


// --------- count_impl main body --------------
Function fn_764 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_778}}};


// --------- conj_impl --------------
Function fn_765;
Value *arityImpl_779(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_700(empty_list, rslt3, (Value *)&protoFn_236);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_396(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- conj_impl main body --------------
Function fn_765 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_779}}};


// --------- reduce_impl --------------
Function fn_766;
Value *arityImpl_780(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_368(empty_list, arg0);
Value *rslt4 = protoFnImpl_230(empty_list, rslt3, arg1, arg2);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- reduce_impl main body --------------
Function fn_766 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_780}}};


// --------- comp*_impl --------------
Function fn_767;
Value *arityImpl_781(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond4 = cond6;
dec_and_free(cond6);
} else {
dec_and_free(rslt5);
incRef(var_76);
cond4 = var_76;
}

if (isTrue(cond4)) {
dec_and_free(cond4);
List *arg11 = (List *)rslt2;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
Value *rslt12 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt13 = arityImpl_716(empty_list, rslt12, (Value *)&fn_152);
List *varArgs14 = empty_list;
incRef((Value *)rslt13);
varArgs14 = (List *)listCons((Value *)rslt13, varArgs14);
Value *rslt15 = arityImpl_186(empty_list, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
Value *rslt16 = arityImpl_646(empty_list, (Value *)&fn_743, rslt15);
Value *rslt17 = arityImpl_162(empty_list, rslt16);
List *varArgs18 = empty_list;
incRef((Value *)rslt17);
varArgs18 = (List *)listCons((Value *)rslt17, varArgs18);
incRef((Value *)(Value *)&fn_164);
varArgs18 = (List *)listCons((Value *)(Value *)&fn_164, varArgs18);
Value *rslt19 = arityImpl_466(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
Value *rslt20 = arityImpl_716(empty_list, rslt12, rslt19);
Value *rslt21 = arityImpl_141(empty_list, rslt20);
incRef(rslt21);
cond3 = rslt21;
dec_and_free(rslt15);
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt13);
dec_and_free(rslt12);
dec_and_free(rslt17);
dec_and_free(rslt21);
dec_and_free(rslt16);
} else {
dec_and_free(cond4);
incRef(arg0);
cond3 = arg0;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- comp*_impl main body --------------
Function fn_767 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_781}}};


// --------- =*_impl --------------
Function fn_768;
Value *arityImpl_785(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_156(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_768 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_785}}};


// --------- string-list_impl --------------
Function fn_769;
Value *arityImpl_786(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_769 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_786}}};


// --------- seq_impl --------------
Function fn_770;
Value *arityImpl_787(List *closures, Value *arg0) {
Value *cond1;
Value *rslt6 = arityImpl_462(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_129);
cond1 = var_129;
} else {
dec_and_free(rslt6);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
Value *rslt4 = protoFnImpl_368(empty_list, rslt3);
Value *rslt5 = arityImpl_132(empty_list, rslt2, rslt4);
incRef(rslt5);
cond1 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- seq_impl main body --------------
Function fn_770 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_787}}};


// --------- m-first_impl --------------
Function fn_771;
Value *arityImpl_788(List *closures, Value *arg0) {
Value *cond1;
Value *rslt4 = arityImpl_462(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef((Value *)&reified_522);
cond1 = (Value *)&reified_522;
} else {
dec_and_free(rslt4);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = protoImpl_599(empty_list, (Value *)&reified_602, rslt2);
incRef(rslt3);
cond1 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- m-first_impl main body --------------
Function fn_771 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_788}}};


// --------- first_impl --------------
Function fn_772;
Value *arityImpl_789(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
return(rslt1);
};


// --------- first_impl main body --------------
Function fn_772 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_789}}};


// --------- rest_impl --------------
Function fn_773;
Value *arityImpl_790(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- rest_impl main body --------------
Function fn_773 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_790}}};


// --------- type-args_impl --------------
Function fn_774;
Value *arityImpl_791(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- type-args_impl main body --------------
Function fn_774 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_791}}};


// --------- sha1_impl --------------
Function fn_792;
Value *arityImpl_805(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_792 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_805}}};


// --------- empty?_impl --------------
Function fn_793;
Value *arityImpl_806(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
Value *rslt2 = arityImpl_462(empty_list, (Value *)&_num_13, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- empty?_impl main body --------------
Function fn_793 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_806}}};


// --------- empty_impl --------------
Function fn_794;
Value *arityImpl_807(List *closures, Value *arg0) {
incRef((Value *)&_str_55);
return((Value *)&_str_55);
};


// --------- empty_impl main body --------------
Function fn_794 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_807}}};


// --------- count_impl --------------
Function fn_795;
Value *arityImpl_808(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
return(rslt1);
};


// --------- count_impl main body --------------
Function fn_795 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_808}}};


// --------- conj_impl --------------
Function fn_796;
Value *arityImpl_809(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_700(empty_list, rslt3, (Value *)&protoFn_236);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_396(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- conj_impl main body --------------
Function fn_796 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_809}}};


// --------- reduce_impl --------------
Function fn_797;
Value *arityImpl_810(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_368(empty_list, arg0);
Value *rslt4 = protoFnImpl_230(empty_list, rslt3, arg1, arg2);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- reduce_impl main body --------------
Function fn_797 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_810}}};


// --------- comp*_impl --------------
Function fn_798;
Value *arityImpl_811(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond4 = cond6;
dec_and_free(cond6);
} else {
dec_and_free(rslt5);
incRef(var_76);
cond4 = var_76;
}

if (isTrue(cond4)) {
dec_and_free(cond4);
List *arg11 = (List *)rslt2;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
Value *rslt12 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt13 = arityImpl_716(empty_list, rslt12, (Value *)&fn_152);
List *varArgs14 = empty_list;
incRef((Value *)rslt13);
varArgs14 = (List *)listCons((Value *)rslt13, varArgs14);
Value *rslt15 = arityImpl_186(empty_list, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
Value *rslt16 = arityImpl_646(empty_list, (Value *)&fn_743, rslt15);
Value *rslt17 = arityImpl_162(empty_list, rslt16);
List *varArgs18 = empty_list;
incRef((Value *)rslt17);
varArgs18 = (List *)listCons((Value *)rslt17, varArgs18);
incRef((Value *)(Value *)&fn_164);
varArgs18 = (List *)listCons((Value *)(Value *)&fn_164, varArgs18);
Value *rslt19 = arityImpl_466(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
Value *rslt20 = arityImpl_716(empty_list, rslt12, rslt19);
Value *rslt21 = arityImpl_141(empty_list, rslt20);
incRef(rslt21);
cond3 = rslt21;
dec_and_free(rslt15);
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt13);
dec_and_free(rslt12);
dec_and_free(rslt17);
dec_and_free(rslt21);
dec_and_free(rslt16);
} else {
dec_and_free(cond4);
incRef(arg0);
cond3 = arg0;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- comp*_impl main body --------------
Function fn_798 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_811}}};


// --------- =*_impl --------------
Function fn_799;
Value *arityImpl_815(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_156(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_799 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_815}}};


// --------- string-list_impl --------------
Function fn_800;
Value *arityImpl_816(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_800 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_816}}};


// --------- seq_impl --------------
Function fn_801;
Value *arityImpl_817(List *closures, Value *arg0) {
Value *cond1;
Value *rslt6 = arityImpl_462(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_129);
cond1 = var_129;
} else {
dec_and_free(rslt6);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
Value *rslt4 = protoFnImpl_368(empty_list, rslt3);
Value *rslt5 = arityImpl_132(empty_list, rslt2, rslt4);
incRef(rslt5);
cond1 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- seq_impl main body --------------
Function fn_801 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_817}}};


// --------- m-first_impl --------------
Function fn_802;
Value *arityImpl_818(List *closures, Value *arg0) {
Value *cond1;
Value *rslt4 = arityImpl_462(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef((Value *)&reified_522);
cond1 = (Value *)&reified_522;
} else {
dec_and_free(rslt4);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = protoImpl_599(empty_list, (Value *)&reified_602, rslt2);
incRef(rslt3);
cond1 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- m-first_impl main body --------------
Function fn_802 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_818}}};


// --------- first_impl --------------
Function fn_803;
Value *arityImpl_819(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
return(rslt1);
};


// --------- first_impl main body --------------
Function fn_803 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_819}}};


// --------- rest_impl --------------
Function fn_804;
Value *arityImpl_820(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- rest_impl main body --------------
Function fn_804 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_820}}};


// --------- str --------------
Function fn_821;
Value *arityImpl_822(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_717(empty_list, arg0);
Value *cond2;
Value *cond3;

if (isTrue((Value *)&trueVal)) {
dec_and_free((Value *)&trueVal);
Value *cond4;
Value *rslt5 = protoFnImpl_222(empty_list, rslt1);
Value *rslt6 = protoFnImpl_200(empty_list, rslt5, (Value *)&_num_1);
dec_and_free(rslt5);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_76);
cond4 = var_76;
} else {
dec_and_free(rslt6);
incRef(var_75);
cond4 = var_75;
}
incRef(cond4);
cond3 = cond4;
dec_and_free(cond4);
} else {
dec_and_free((Value *)&trueVal);
incRef(var_76);
cond3 = var_76;
}

if (isTrue(cond3)) {
dec_and_free(cond3);
List *arg9 = (List *)rslt1;
Value *arg7 = arg9->head;
if (arg9->tail) arg9->tail->len = arg9->len - 1;
arg9 = arg9->tail;
Value *arg8 = (Value *) arg9;
Value *rslt10 = arityImpl_700(empty_list, arg0, (Value *)&protoFn_236);
Value *rslt11 = arityImpl_716(empty_list, rslt10, (Value *)&fn_152);
List *varArgs12 = empty_list;
incRef((Value *)rslt11);
varArgs12 = (List *)listCons((Value *)rslt11, varArgs12);
Value *rslt13 = arityImpl_186(empty_list, (Value *)varArgs12);
dec_and_free((Value *)varArgs12);
Value *rslt14 = arityImpl_646(empty_list, (Value *)&fn_743, rslt13);
Value *rslt15 = arityImpl_162(empty_list, rslt14);
List *varArgs16 = empty_list;
incRef((Value *)rslt15);
varArgs16 = (List *)listCons((Value *)rslt15, varArgs16);
incRef((Value *)(Value *)&fn_164);
varArgs16 = (List *)listCons((Value *)(Value *)&fn_164, varArgs16);
Value *rslt17 = arityImpl_466(empty_list, (Value *)varArgs16);
dec_and_free((Value *)varArgs16);
Value *rslt18 = arityImpl_716(empty_list, rslt10, rslt17);
Value *rslt19 = arityImpl_141(empty_list, rslt18);
incRef(rslt19);
cond2 = rslt19;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(rslt19);
dec_and_free(rslt18);
dec_and_free(rslt10);
dec_and_free(rslt13);
dec_and_free(rslt11);
dec_and_free(rslt17);
} else {
dec_and_free(cond3);
incRef((Value *)&_str_55);
cond2 = (Value *)&_str_55;
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};

// --------- str main body --------------
Function fn_821 = {FunctionType, -1, "str", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_822}}};


// --------- take --------------
Function fn_827;
Value *arityImpl_828(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt16 = arityImpl_623(empty_list, arg1, (Value *)&_num_1);

if (isTrue(rslt16)) {
dec_and_free(rslt16);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt16);
Value *rslt3 = protoFnImpl_27(empty_list, arg0);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *cond7;
Value *rslt8 = protoFnImpl_222(empty_list, rslt3);
Value *rslt9 = protoFnImpl_200(empty_list, rslt8, (Value *)&_num_1);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(var_76);
cond7 = var_76;
} else {
dec_and_free(rslt9);
incRef(var_75);
cond7 = var_75;
}
incRef(cond7);
cond5 = cond7;
dec_and_free(cond7);
} else {
dec_and_free(rslt6);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg12 = (List *)rslt3;
Value *arg10 = arg12->head;
if (arg12->tail) arg12->tail->len = arg12->len - 1;
arg12 = arg12->tail;
Value *arg11 = (Value *) arg12;
Value *rslt13 = arityImpl_754(empty_list, arg1);
Value *rslt14 = arityImpl_828(closures, arg11, rslt13);
Value *rslt15 = arityImpl_132(empty_list, arg10, rslt14);
incRef(rslt15);
cond4 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(rslt13);
} else {
dec_and_free(cond5);
incRef(var_129);
cond4 = var_129;
}
incRef(cond4);
cond2 = cond4;
dec_and_free(cond4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- take main body --------------
Function fn_827 = {FunctionType, -1, "take", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_828}}};


// --------- drop --------------
Function fn_833;
Value *arityImpl_834(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt6 = arityImpl_623(empty_list, arg1, (Value *)&_num_1);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt6);
Value *rslt3 = protoFnImpl_366(empty_list, arg0);
Value *rslt4 = arityImpl_754(empty_list, arg1);
Value *rslt5 = arityImpl_834(closures, rslt3, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- drop main body --------------
Function fn_833 = {FunctionType, -1, "drop", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_834}}};


// --------- split --------------
Function fn_836;
Value *arityImpl_837(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt9 = arityImpl_623(empty_list, arg1, (Value *)&_num_1);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
Value *rslt10 = arityImpl_233(empty_list, arg2);
List *varArgs11 = empty_list;
incRef((Value *)arg0);
varArgs11 = (List *)listCons((Value *)arg0, varArgs11);
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
Value *rslt12 = arityImpl_186(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
incRef(rslt12);
cond3 = rslt12;
dec_and_free(rslt10);
dec_and_free(rslt12);
} else {
dec_and_free(rslt9);
Value *rslt13 = protoFnImpl_228(empty_list, arg0);

if (isTrue(rslt13)) {
dec_and_free(rslt13);
Value *rslt14 = arityImpl_233(empty_list, arg2);
List *varArgs15 = empty_list;
incRef((Value *)arg0);
varArgs15 = (List *)listCons((Value *)arg0, varArgs15);
incRef((Value *)rslt14);
varArgs15 = (List *)listCons((Value *)rslt14, varArgs15);
Value *rslt16 = arityImpl_186(empty_list, (Value *)varArgs15);
dec_and_free((Value *)varArgs15);
incRef(rslt16);
cond3 = rslt16;
dec_and_free(rslt14);
dec_and_free(rslt16);
} else {
dec_and_free(rslt13);
Value *rslt4 = protoFnImpl_366(empty_list, arg0);
Value *rslt5 = arityImpl_754(empty_list, arg1);
Value *rslt6 = protoFnImpl_370(empty_list, arg0);
Value *rslt7 = arityImpl_132(empty_list, rslt6, arg2);
Value *rslt8 = arityImpl_837(closures, rslt4, rslt5, rslt7);
incRef(rslt8);
cond3 = rslt8;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
}
return(cond3);
};

Value *arityImpl_838(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
FnArity *arity2 = findFnArity((Value *)&fn_836, 3);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType3 *fn4 = (FnType3 *)arity2->fn;
rslt5 = fn4(arity2->closures, arg0, arg1, var_129);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(var_129);
varArgs3 = (List *)listCons(var_129, varArgs3);
incRef(arg1);
varArgs3 = (List *)listCons(arg1, varArgs3);
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_836)->name);
  abort();
}
return(rslt5);
};


// --------- split main body --------------
Function fn_836 = {FunctionType, -1, "split", 2, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_837}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_838}}};


// --------- partition --------------
Function fn_840;
Value *arityImpl_841(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = protoFnImpl_222(empty_list, arg0);
Value *rslt8 = arityImpl_623(empty_list, rslt7, arg1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt8);
Value *rslt3 = arityImpl_828(empty_list, arg0, arg1);
Value *rslt4 = arityImpl_834(empty_list, arg0, arg1);
Value *rslt5 = arityImpl_841(closures, rslt4, arg1);
Value *rslt6 = arityImpl_132(empty_list, rslt3, rslt5);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- partition main body --------------
Function fn_840 = {FunctionType, -1, "partition", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_841}}};


// --------- partition-all --------------
Function fn_843;
Value *arityImpl_844(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = protoFnImpl_222(empty_list, arg0);
Value *rslt8 = arityImpl_623(empty_list, rslt7, arg1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
List *varArgs9 = empty_list;
incRef((Value *)arg0);
varArgs9 = (List *)listCons((Value *)arg0, varArgs9);
Value *rslt10 = arityImpl_186(empty_list, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
incRef(rslt10);
cond2 = rslt10;
dec_and_free(rslt10);
} else {
dec_and_free(rslt8);
Value *rslt3 = arityImpl_828(empty_list, arg0, arg1);
Value *rslt4 = arityImpl_834(empty_list, arg0, arg1);
Value *rslt5 = arityImpl_844(closures, rslt4, arg1);
Value *rslt6 = arityImpl_132(empty_list, rslt3, rslt5);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- partition-all main body --------------
Function fn_843 = {FunctionType, -1, "partition-all", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_844}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_56 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_846;
Value *arityImpl_847(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_368(empty_list, arg0);
Value *rslt3 = protoFnImpl_27(empty_list, rslt2);
Value *cond4;
Value *cond8;
Value *rslt9 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt2);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
Value *cond10;
Value *rslt11 = protoFnImpl_222(empty_list, rslt3);
Value *rslt12 = protoFnImpl_200(empty_list, rslt11, (Value *)&_num_1);
dec_and_free(rslt11);

if (isTrue(rslt12)) {
dec_and_free(rslt12);
incRef(var_76);
cond10 = var_76;
} else {
dec_and_free(rslt12);
incRef(var_75);
cond10 = var_75;
}
incRef(cond10);
cond8 = cond10;
dec_and_free(cond10);
} else {
dec_and_free(rslt9);
incRef(var_76);
cond8 = var_76;
}

if (isTrue(cond8)) {
dec_and_free(cond8);
List *arg15 = (List *)rslt3;
Value *arg13 = arg15->head;
if (arg15->tail) arg15->tail->len = arg15->len - 1;
arg15 = arg15->tail;
Value *arg14 = (Value *) arg15;
Value *cond16;
Value *rslt21 = arityImpl_462(empty_list, arg1, (Value *)&_num_13);

if (isTrue(rslt21)) {
dec_and_free(rslt21);
incRef(arg13);
cond16 = arg13;
} else {
dec_and_free(rslt21);
Value *rslt17 = protoFnImpl_368(empty_list, arg0);
Value *rslt18 = protoFnImpl_366(empty_list, rslt17);
Value *rslt19 = arityImpl_754(empty_list, arg1);
Value *rslt20 = arityImpl_847(closures, rslt18, rslt19);
incRef(rslt20);
cond16 = rslt20;
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt18);
dec_and_free(rslt17);
}
incRef(cond16);
cond4 = cond16;
dec_and_free(cond16);
} else {
dec_and_free(cond8);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_56);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_56, varArgs5);
Value *rslt6 = arityImpl_739(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = arityImpl_96(empty_list);
incRef(rslt7);
cond4 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(cond4);
};

Value *arityImpl_848(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_368(empty_list, arg0);
Value *rslt4 = protoFnImpl_27(empty_list, rslt3);
Value *cond5;
Value *cond6;
Value *rslt7 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt3);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
Value *cond8;
Value *rslt9 = protoFnImpl_222(empty_list, rslt4);
Value *rslt10 = protoFnImpl_200(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_76);
cond8 = var_76;
} else {
dec_and_free(rslt10);
incRef(var_75);
cond8 = var_75;
}
incRef(cond8);
cond6 = cond8;
dec_and_free(cond8);
} else {
dec_and_free(rslt7);
incRef(var_76);
cond6 = var_76;
}

if (isTrue(cond6)) {
dec_and_free(cond6);
List *arg13 = (List *)rslt4;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *cond14;
Value *rslt22 = arityImpl_462(empty_list, arg1, (Value *)&_num_13);

if (isTrue(rslt22)) {
dec_and_free(rslt22);
incRef(arg11);
cond14 = arg11;
} else {
dec_and_free(rslt22);
Value *rslt15 = protoFnImpl_368(empty_list, arg0);
Value *rslt16 = protoFnImpl_366(empty_list, rslt15);
Value *rslt17 = arityImpl_754(empty_list, arg1);
Value *rslt21;
FnArity *arity18 = findFnArity((Value *)&fn_846, 2);
if(arity18 != (FnArity *)0 && !arity18->variadic) {
FnType2 *fn20 = (FnType2 *)arity18->fn;
rslt21 = fn20(arity18->closures, rslt16, rslt17);
} else if(arity18 != (FnArity *)0 && arity18->variadic) {
FnType1 *fn20 = (FnType1 *)arity18->fn;
List *varArgs19 = empty_list;
incRef(rslt17);
varArgs19 = (List *)listCons(rslt17, varArgs19);
incRef(rslt16);
varArgs19 = (List *)listCons(rslt16, varArgs19);
rslt21 = fn20(arity18->closures, (Value *)varArgs19);
dec_and_free((Value *)varArgs19);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_846)->name);
  abort();
}
incRef(rslt21);
cond14 = rslt21;
dec_and_free(rslt15);
dec_and_free(rslt17);
dec_and_free(rslt21);
dec_and_free(rslt16);
}
incRef(cond14);
cond5 = cond14;
dec_and_free(cond14);
} else {
dec_and_free(cond6);
incRef(arg2);
cond5 = arg2;
}
incRef(cond5);
dec_and_free(cond5);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(cond5);
};


// --------- nth main body --------------
Function fn_846 = {FunctionType, -1, "nth", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_847}, &(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_848}}};


// --------- last --------------
Function fn_856;
Value *arityImpl_857(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_222(empty_list, arg0);
Value *rslt3 = arityImpl_754(empty_list, rslt2);
Value *rslt4 = arityImpl_847(empty_list, arg0, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};


// --------- last main body --------------
Function fn_856 = {FunctionType, -1, "last", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_857}}};


// --------- butlast --------------
Function fn_859;
Value *arityImpl_860(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_27(empty_list, arg0);
Value *cond2;
Value *cond3;
Value *rslt4 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
Value *cond5;
Value *rslt6 = protoFnImpl_222(empty_list, rslt1);
Value *rslt7 = protoFnImpl_200(empty_list, rslt6, (Value *)&_num_1);
dec_and_free(rslt6);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(var_76);
cond5 = var_76;
} else {
dec_and_free(rslt7);
incRef(var_75);
cond5 = var_75;
}
incRef(cond5);
cond3 = cond5;
dec_and_free(cond5);
} else {
dec_and_free(rslt4);
incRef(var_76);
cond3 = var_76;
}

if (isTrue(cond3)) {
dec_and_free(cond3);
List *arg10 = (List *)rslt1;
Value *arg8 = arg10->head;
if (arg10->tail) arg10->tail->len = arg10->len - 1;
arg10 = arg10->tail;
Value *arg9 = (Value *) arg10;
Value *rslt11 = protoFnImpl_222(empty_list, arg0);
Value *rslt12 = arityImpl_754(empty_list, rslt11);
Value *rslt13 = arityImpl_838(empty_list, arg0, rslt12);
Value *rslt14 = arityImpl_141(empty_list, rslt13);
incRef(rslt14);
cond2 = rslt14;
dec_and_free(rslt14);
dec_and_free(rslt13);
dec_and_free(rslt11);
dec_and_free(rslt12);
} else {
dec_and_free(cond3);
incRef(arg0);
cond2 = arg0;
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};


// --------- butlast main body --------------
Function fn_859 = {FunctionType, -1, "butlast", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_860}}};


BitmapIndexedNode emptyBMI = {BitmapIndexedType, -1, 0, 0};

BitmapIndexedNode *clone_BitmapIndexedNode(BitmapIndexedNode *node, int idx,
                                           Value *key, Value* val)
{
  int itemCount = __builtin_popcount(node->bitmap);
  BitmapIndexedNode *newNode = malloc_bmiNode(itemCount);
  newNode->type = BitmapIndexedType;
  newNode->refs = 1;
  newNode->bitmap = node->bitmap;
  for (int i = 0; i < itemCount; i++) {
    if (i == idx) {
      newNode->array[i * 2] = key;
      newNode->array[i * 2 + 1] = val;
    } else {
      if (node->array[i * 2] != (Value *)0)
        incRef(node->array[i * 2]);
      if (node->array[i * 2 + 1] != (Value *)0)
        incRef(node->array[i * 2 + 1]);
      newNode->array[i * 2] = node->array[i * 2];
      newNode->array[i * 2 + 1] = node->array[i * 2 + 1];
    }
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
  BitmapIndexedNode *newNode = malloc_bmiNode(2);
  newNode->type = BitmapIndexedType;
  newNode->refs = 1;
  int key1bit = bitpos(key1hash, shift);
  int key2bit = bitpos(key2hash, shift);
  newNode->bitmap = key1bit | key2bit;
  int key1idx = __builtin_popcount(newNode->bitmap & (key1bit - 1));
  int key2idx = __builtin_popcount(newNode->bitmap & (key2bit - 1));
  if (key1bit == key2bit) {
    newNode->array[0] = (Value *)0;
    newNode->array [1] = createNode(shift + 5, key1hash, key1, val1,
                                               key2hash, key2, val2);
  } else {
    incRef(key1);
    incRef(val1);
    incRef(key2);
    incRef(val2);
    newNode->array[key1idx * 2] = key1;
    newNode->array[key1idx * 2 + 1] = val1;
    newNode->array[key2idx * 2] = key2;
    newNode->array[key2idx * 2 + 1] = val2;
  }
  return((Value *)newNode);
}
Value *var_865 = (Value *)&emptyBMI;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_59 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_58 = {1, -1, 1,"}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_57 = {1, -1, 1,"{"};

// --------- count_impl --------------
Function fn_866;
Value *arityImpl_879(List *closures, Value *arg0) {

int cnt = __builtin_popcount(((BitmapIndexedNode *)arg0)->bitmap);
int accum = 0;
for(int i = 0; i < cnt; i++) {
  if (((BitmapIndexedNode *)arg0)->array[i * 2] == (Value *)0) {
    Number *subCnt = (Number *)count(((BitmapIndexedNode *)arg0)->array[i * 2 + 1]);
    accum += subCnt->numVal;
    dec_and_free((Value *)subCnt);
  } else {
    accum++;
  }
}
return(numberValue(accum));
};


// --------- count_impl main body --------------
Function fn_866 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_879}}};


// --------- empty?_impl --------------
Function fn_867;
Value *arityImpl_880(List *closures, Value *arg0) {

if (((BitmapIndexedNode *)arg0)->bitmap == 0)
   return(true);
else
   return(false);
};


// --------- empty?_impl main body --------------
Function fn_867 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_880}}};


// --------- zero_impl --------------
Function fn_868;
Value *arityImpl_881(List *closures, Value *arg0) {
incRef(var_865);
return(var_865);
};


// --------- zero_impl main body --------------
Function fn_868 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_881}}};


// --------- comp*_impl --------------
Function fn_869;

// --------- anon --------------
Function fn_883;

// --------- anon --------------
Function fn_885;
Value *arityImpl_886(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_646(empty_list, (Value *)&protoFn_427, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_885 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_886}}};

Value *arityImpl_884(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_368(empty_list, arg1);
Value *rslt4 = protoFnImpl_230(empty_list, rslt2, arg0, (Value *)&fn_885);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt4);
};


// --------- anon main body --------------
Function fn_883 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_884}}};

Value *arityImpl_882(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_230(empty_list, arg1, arg0, (Value *)&fn_883);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_869 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_882}}};


// --------- get_impl --------------
Function fn_870;
Value *arityImpl_887(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_870 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_887}}};


// --------- keys_impl --------------
Function fn_871;
Value *arityImpl_888(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_337(empty_list, rslt1, (Value *)&protoFn_358);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keys_impl main body --------------
Function fn_871 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_888}}};


// --------- vals_impl --------------
Function fn_872;
Value *arityImpl_889(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_337(empty_list, rslt1, (Value *)&fn_377);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- vals_impl main body --------------
Function fn_872 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_889}}};


// --------- assoc_impl --------------
Function fn_873;
Value *arityImpl_890(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_873 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_890}}};


// --------- string-list_impl --------------
Function fn_874;

// --------- anon --------------
Function fn_895;
Value *arityImpl_896(List *closures, Value *arg2) {
List *arg3 = (List *)arg2;
Value *arg0 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *arg1 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *rslt4 = protoFnImpl_239(empty_list, arg0);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_52, varArgs5);
Value *rslt6 = arityImpl_186(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_239(empty_list, arg1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_186(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_396(empty_list, rslt4, rslt9);
incRef(rslt10);
dec_and_free(rslt6);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt10);
};


// --------- anon main body --------------
Function fn_895 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_896}}};

Value *arityImpl_891(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_27(empty_list, rslt1);
Value *cond3;
Value *cond6;
Value *rslt7 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
Value *cond8;
Value *rslt9 = protoFnImpl_222(empty_list, rslt2);
Value *rslt10 = protoFnImpl_200(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_76);
cond8 = var_76;
} else {
dec_and_free(rslt10);
incRef(var_75);
cond8 = var_75;
}
incRef(cond8);
cond6 = cond8;
dec_and_free(cond8);
} else {
dec_and_free(rslt7);
incRef(var_76);
cond6 = var_76;
}

if (isTrue(cond6)) {
dec_and_free(cond6);
List *arg13 = (List *)rslt2;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *rslt15 = protoFnImpl_337(empty_list, rslt1, (Value *)&fn_895);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_57, varArgs16);
Value *rslt17 = arityImpl_186(empty_list, (Value *)varArgs16);
dec_and_free((Value *)varArgs16);
List *varArgs18 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs18 = (List *)listCons((Value *)(Value *)&_str_50, varArgs18);
Value *rslt19 = arityImpl_186(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
Value *rslt20 = arityImpl_719(empty_list, rslt15, rslt19);
List *varArgs21 = empty_list;
incRef((Value *)rslt20);
varArgs21 = (List *)listCons((Value *)rslt20, varArgs21);
Value *rslt22 = arityImpl_186(empty_list, (Value *)varArgs21);
dec_and_free((Value *)varArgs21);
Value *rslt23 = arityImpl_646(empty_list, (Value *)&fn_407, rslt22);
List *varArgs24 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs24 = (List *)listCons((Value *)(Value *)&_str_58, varArgs24);
Value *rslt25 = arityImpl_186(empty_list, (Value *)varArgs24);
dec_and_free((Value *)varArgs24);
List *varArgs26 = empty_list;
incRef((Value *)rslt25);
varArgs26 = (List *)listCons((Value *)rslt25, varArgs26);
incRef((Value *)rslt23);
varArgs26 = (List *)listCons((Value *)rslt23, varArgs26);
Value *rslt27 = arityImpl_186(empty_list, (Value *)varArgs26);
dec_and_free((Value *)varArgs26);
Value *rslt28 = arityImpl_706(empty_list, rslt17, rslt27);
incRef(rslt28);
cond3 = rslt28;
dec_and_free(rslt15);
dec_and_free(rslt27);
dec_and_free(rslt28);
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt22);
dec_and_free(rslt17);
dec_and_free(rslt25);
dec_and_free(rslt23);
} else {
dec_and_free(cond6);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_59, varArgs4);
Value *rslt5 = arityImpl_186(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
incRef(rslt5);
cond3 = rslt5;
dec_and_free(rslt5);
}
incRef(cond3);
dec_and_free(rslt1);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- string-list_impl main body --------------
Function fn_874 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_891}}};


// --------- seq_impl --------------
Function fn_875;
Value *arityImpl_897(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_424(empty_list, arg0, var_129);
return(rslt1);
};


// --------- seq_impl main body --------------
Function fn_875 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_897}}};


// --------- hash-seq_impl --------------
Function fn_876;
Value *arityImpl_898(List *closures, Value *arg0, Value *arg1) {

BitmapIndexedNode *node = (BitmapIndexedNode *)arg0;
int cnt = __builtin_popcount(node->bitmap);
List *seq = (List *)arg1;
for (int i = 0; i < cnt; i++) {
   if (node->array[2 * i] == (Value *)0) {
     seq = (List *)hashSeq(node->array[2 * i + 1], (Value *)seq);
   } else {
     List *pair = listCons(node->array[2 * i], listCons(node->array[2 * i + 1], empty_list));
     incRef(node->array[2 * i]);
     incRef(node->array[2 * i + 1]);
     seq = listCons((Value *)pair, seq);
   }
}
return((Value *)seq);
};


// --------- hash-seq_impl main body --------------
Function fn_876 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_898}}};


// --------- assoc*_impl --------------
Function fn_877;
Value *arityImpl_899(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

BitmapIndexedNode *node = (BitmapIndexedNode *)arg0;
Value *key = arg1;
Value *val = arg2;
int64_t hash = ((Number *)arg3)->numVal;
int shift = (int)((Number *)arg4)->numVal;

int bit = bitpos(hash, shift);
int idx = __builtin_popcount(node->bitmap & (bit - 1));
if (node->bitmap & bit) {
  // if the hash position is already filled
  Value *keyOrNull = node->array[2 * idx];
  Value *valOrNode = node->array[2 * idx + 1];
  if (keyOrNull == (Value *)0) {
    // There is no key in the position, so valOrNode is
    // pointer to a node.
    Value *newShift = (Value *)numberValue(shift + 5);
    Value *n = assoc(valOrNode, key, val, arg3, newShift);
    dec_and_free(newShift);
    if (n == valOrNode) {
      // the key was already associated with the value
      // so do nothing
      dec_and_free(n);
      incRef(arg0);
      return(arg0);
    } else {
      // clone node and add n to it
      BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node, idx, (Value *)0, n);
      return((Value *)newNode);
    }
  } else if (equal(key, keyOrNull)) {
    // if the keyOrNull points to a value that is equal to key
    // create new hash-map with valOrNode replaced by val
    // clone node and add val to it
    BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node, idx, key, val);
    incRef((Value *)key);
    incRef((Value *)val);
    return((Value *)newNode);
  } else {
    // there is already a key/val pair at the position where key
    // would be placed. Extend tree a level
    Value *hashValue = sha1(keyOrNull);
    int64_t existingKeyHash = ((Number *)hashValue)->numVal;
    if (existingKeyHash == hash) {
      // make & return HashCollisionNode
      HashCollisionNode *newLeaf = malloc_hashCollisionNode(2);
      newLeaf->array[0] = keyOrNull;
      newLeaf->array[1] = valOrNode;
      newLeaf->array[2] = key;
      newLeaf->array[3] = val;
      incRef((Value *)keyOrNull);
      incRef((Value *)valOrNode);
      incRef((Value *)key);
      incRef((Value *)val);

      BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node, idx, (Value *)0, (Value *)newLeaf);
      dec_and_free(hashValue);
      return((Value *)newNode);
    } else {
      Value *newLeaf = createNode(shift + 5,
                                  existingKeyHash, keyOrNull, valOrNode,
                                  hash, key, val);
      BitmapIndexedNode *newNode = clone_BitmapIndexedNode(node, idx, (Value *)0, newLeaf);
      dec_and_free(hashValue);
      return((Value *)newNode);
    }
  }
} else {
  // the position in the node is empty
  int n = __builtin_popcount(node->bitmap);
  if (n >= 16) {
    ArrayNode *newNode = (ArrayNode *)malloc_arrayNode();
    int jdx = mask(hash, shift);
    Value *newShift = (Value *)numberValue(shift + 5);
    newNode->array[jdx] = assoc((Value *)&emptyBMI, key, val, arg3, newShift);
    for (int i = 0, j = 0; i < 32; i++) {
      if ((node->bitmap >> i) & 1) {
        if (node->array[j] == (Value *)0) {
          newNode->array[i] = node->array[j + 1];
          incRef(newNode->array[i]);
        } else {
          Value *hash = sha1(node->array[j]);
          newNode->array[i] = assoc((Value *)&emptyBMI, node->array[j], node->array[j + 1], hash, newShift);
          dec_and_free(hash);
        }
        j += 2;
      }
    }
    dec_and_free(newShift);
    return((Value *)newNode);
  } else {
    int itemCount = n + 1;
    BitmapIndexedNode *newNode = malloc_bmiNode(itemCount);
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
Function fn_877 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_899}}};


// --------- get*_impl --------------
Function fn_878;
Value *arityImpl_900(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

BitmapIndexedNode *node = (BitmapIndexedNode *)arg0;
Value *key = arg1;
int64_t hash = ((Number *)arg3)->numVal;
int shift = (int)((Number *)arg4)->numVal;

int bit = bitpos(hash, shift);
int idx = __builtin_popcount(node->bitmap & (bit - 1));
if (node->bitmap & bit) {
  // if the hash position is already filled
  Value *keyOrNull = node->array[2 * idx];
  Value *valOrNode = node->array[2 * idx + 1];
  if (keyOrNull == (Value *)0) {
    // There is no key in the position, so valOrNode is
    // pointer to a node.
    Value *newShift = (Value *)numberValue(shift + 5);
    Value *v = get(valOrNode, key, arg2, arg3, newShift);
    dec_and_free(newShift);
    return(v);
  } else {
    if (equal(key, keyOrNull)) {
      // fprintf(stderr, "Found at: %d\n", idx);
      incRef(valOrNode);
      return(valOrNode);
    } else {
      incRef(arg2);
      return(arg2);
    }
  }
} else {
  incRef(arg2);
  return(arg2);
}
};


// --------- get*_impl main body --------------
Function fn_878 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_900}}};


// --------- count_impl --------------
Function fn_901;
Value *arityImpl_914(List *closures, Value *arg0) {

int accum = 0;
for(int i = 0; i < 32; i++){
  if (((ArrayNode *)arg0)->array[i] != (Value *)0) {
    Number *subCnt = (Number *)count(((ArrayNode *)arg0)->array[i]);
    accum += subCnt->numVal;
    dec_and_free((Value *)subCnt);
  }
}
return(numberValue(accum));
};


// --------- count_impl main body --------------
Function fn_901 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_914}}};


// --------- empty?_impl --------------
Function fn_902;
Value *arityImpl_915(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};


// --------- empty?_impl main body --------------
Function fn_902 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_915}}};


// --------- zero_impl --------------
Function fn_903;
Value *arityImpl_916(List *closures, Value *arg0) {
incRef(var_865);
return(var_865);
};


// --------- zero_impl main body --------------
Function fn_903 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_916}}};


// --------- comp*_impl --------------
Function fn_904;

// --------- anon --------------
Function fn_918;

// --------- anon --------------
Function fn_920;
Value *arityImpl_921(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_646(empty_list, (Value *)&protoFn_427, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_920 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_921}}};

Value *arityImpl_919(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_368(empty_list, arg1);
Value *rslt4 = protoFnImpl_230(empty_list, rslt2, arg0, (Value *)&fn_920);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt4);
};


// --------- anon main body --------------
Function fn_918 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_919}}};

Value *arityImpl_917(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_230(empty_list, arg1, arg0, (Value *)&fn_918);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_904 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_917}}};


// --------- get_impl --------------
Function fn_905;
Value *arityImpl_922(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_905 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_922}}};


// --------- keys_impl --------------
Function fn_906;
Value *arityImpl_923(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_337(empty_list, rslt1, (Value *)&protoFn_358);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keys_impl main body --------------
Function fn_906 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_923}}};


// --------- vals_impl --------------
Function fn_907;
Value *arityImpl_924(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_337(empty_list, rslt1, (Value *)&fn_377);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- vals_impl main body --------------
Function fn_907 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_924}}};


// --------- assoc_impl --------------
Function fn_908;
Value *arityImpl_925(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_908 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_925}}};


// --------- string-list_impl --------------
Function fn_909;

// --------- anon --------------
Function fn_930;
Value *arityImpl_931(List *closures, Value *arg2) {
List *arg3 = (List *)arg2;
Value *arg0 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *arg1 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *rslt4 = protoFnImpl_239(empty_list, arg0);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_52, varArgs5);
Value *rslt6 = arityImpl_186(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_239(empty_list, arg1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_186(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_396(empty_list, rslt4, rslt9);
incRef(rslt10);
dec_and_free(rslt6);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt10);
};


// --------- anon main body --------------
Function fn_930 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_931}}};

Value *arityImpl_926(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_27(empty_list, rslt1);
Value *cond3;
Value *cond6;
Value *rslt7 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
Value *cond8;
Value *rslt9 = protoFnImpl_222(empty_list, rslt2);
Value *rslt10 = protoFnImpl_200(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_76);
cond8 = var_76;
} else {
dec_and_free(rslt10);
incRef(var_75);
cond8 = var_75;
}
incRef(cond8);
cond6 = cond8;
dec_and_free(cond8);
} else {
dec_and_free(rslt7);
incRef(var_76);
cond6 = var_76;
}

if (isTrue(cond6)) {
dec_and_free(cond6);
List *arg13 = (List *)rslt2;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *rslt15 = protoFnImpl_337(empty_list, rslt1, (Value *)&fn_930);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_57, varArgs16);
Value *rslt17 = arityImpl_186(empty_list, (Value *)varArgs16);
dec_and_free((Value *)varArgs16);
List *varArgs18 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs18 = (List *)listCons((Value *)(Value *)&_str_50, varArgs18);
Value *rslt19 = arityImpl_186(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
Value *rslt20 = arityImpl_719(empty_list, rslt15, rslt19);
List *varArgs21 = empty_list;
incRef((Value *)rslt20);
varArgs21 = (List *)listCons((Value *)rslt20, varArgs21);
Value *rslt22 = arityImpl_186(empty_list, (Value *)varArgs21);
dec_and_free((Value *)varArgs21);
Value *rslt23 = arityImpl_646(empty_list, (Value *)&fn_407, rslt22);
List *varArgs24 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs24 = (List *)listCons((Value *)(Value *)&_str_58, varArgs24);
Value *rslt25 = arityImpl_186(empty_list, (Value *)varArgs24);
dec_and_free((Value *)varArgs24);
List *varArgs26 = empty_list;
incRef((Value *)rslt25);
varArgs26 = (List *)listCons((Value *)rslt25, varArgs26);
incRef((Value *)rslt23);
varArgs26 = (List *)listCons((Value *)rslt23, varArgs26);
Value *rslt27 = arityImpl_186(empty_list, (Value *)varArgs26);
dec_and_free((Value *)varArgs26);
Value *rslt28 = arityImpl_706(empty_list, rslt17, rslt27);
incRef(rslt28);
cond3 = rslt28;
dec_and_free(rslt15);
dec_and_free(rslt27);
dec_and_free(rslt28);
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt22);
dec_and_free(rslt17);
dec_and_free(rslt25);
dec_and_free(rslt23);
} else {
dec_and_free(cond6);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_59, varArgs4);
Value *rslt5 = arityImpl_186(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
incRef(rslt5);
cond3 = rslt5;
dec_and_free(rslt5);
}
incRef(cond3);
dec_and_free(rslt1);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- string-list_impl main body --------------
Function fn_909 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_926}}};


// --------- seq_impl --------------
Function fn_910;
Value *arityImpl_932(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_424(empty_list, arg0, var_129);
return(rslt1);
};


// --------- seq_impl main body --------------
Function fn_910 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_932}}};


// --------- hash-seq_impl --------------
Function fn_911;
Value *arityImpl_933(List *closures, Value *arg0, Value *arg1) {

ArrayNode *node = (ArrayNode *)arg0;
List *seq = (List *)arg1;
for (int i = 0; i < 32; i++) {
   if (node->array[i] != (Value *)0)
     seq = (List *)hashSeq(node->array[i], (Value *)seq);
}
return((Value *)seq);
};


// --------- hash-seq_impl main body --------------
Function fn_911 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_933}}};


// --------- assoc*_impl --------------
Function fn_912;
Value *arityImpl_934(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

ArrayNode *node = (ArrayNode *)arg0;
Value *key = arg1;
Value *val = arg2;
int64_t hash = ((Number *)arg3)->numVal;
int shift = (int)((Number *)arg4)->numVal;
int idx = mask(hash, shift);
Value *newShift = (Value *)numberValue(shift + 5);
ArrayNode *newNode;

Value *subNode = node->array[idx];
if (subNode == (Value *)0) {
  newNode = (ArrayNode *)malloc_arrayNode();
  for (int i = 0; i < 32; i++) {
    if (node->array[i] != (Value *)0) {
      newNode->array[i] = node->array[i];
      incRef(newNode->array[i]);
    }
  }
  Value *hash = sha1(key);
  if (newNode->array[idx] != (Value *)0)
    decRef(newNode->array[idx]);
  newNode->array[idx] = assoc((Value *)&emptyBMI, key, val, hash, newShift);
  dec_and_free(hash);
} else {
    Value *hash = sha1(key);
    Value *n = assoc(subNode, key, val, hash, newShift);
    newNode = (ArrayNode *)malloc_arrayNode();
    for (int i = 0; i < 32; i++) {
      if (i != idx && node->array[i] != (Value *)0) {
        newNode->array[i] = node->array[i];
        incRef(newNode->array[i]);
      }
    }
    if (newNode->array[idx] != (Value *)0)
      decRef(newNode->array[idx]);
    newNode->array[idx] = n;
    dec_and_free(hash);
}
dec_and_free(newShift);
return((Value *)newNode);
};


// --------- assoc*_impl main body --------------
Function fn_912 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_934}}};


// --------- get*_impl --------------
Function fn_913;
Value *arityImpl_935(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

ArrayNode *node = (ArrayNode *)arg0;
Value *key = arg1;
Value *val = arg2;
int64_t hash = ((Number *)arg3)->numVal;
int shift = (int)((Number *)arg4)->numVal;
int idx = mask(hash, shift);
Value *newShift = (Value *)numberValue(shift + 5);
Value* found;

Value *subNode = node->array[idx];
if (subNode == (Value *)0) {
  found = val;
} else {
  found = get(subNode, key, val, arg3, newShift);
}
dec_and_free(newShift);
return((Value *)found);
};


// --------- get*_impl main body --------------
Function fn_913 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_935}}};


// --------- count_impl --------------
Function fn_936;
Value *arityImpl_949(List *closures, Value *arg0) {

return(numberValue(((HashCollisionNode *) arg0)->count / 2));
};


// --------- count_impl main body --------------
Function fn_936 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_949}}};


// --------- empty?_impl --------------
Function fn_937;
Value *arityImpl_950(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};


// --------- empty?_impl main body --------------
Function fn_937 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_950}}};


// --------- zero_impl --------------
Function fn_938;
Value *arityImpl_951(List *closures, Value *arg0) {
incRef(var_865);
return(var_865);
};


// --------- zero_impl main body --------------
Function fn_938 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_951}}};


// --------- comp*_impl --------------
Function fn_939;

// --------- anon --------------
Function fn_953;

// --------- anon --------------
Function fn_955;
Value *arityImpl_956(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_646(empty_list, (Value *)&protoFn_427, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_955 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_956}}};

Value *arityImpl_954(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_368(empty_list, arg1);
Value *rslt4 = protoFnImpl_230(empty_list, rslt2, arg0, (Value *)&fn_955);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt4);
};


// --------- anon main body --------------
Function fn_953 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_954}}};

Value *arityImpl_952(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_230(empty_list, arg1, arg0, (Value *)&fn_953);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_939 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_952}}};


// --------- get_impl --------------
Function fn_940;
Value *arityImpl_957(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_940 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_957}}};


// --------- keys_impl --------------
Function fn_941;
Value *arityImpl_958(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_337(empty_list, rslt1, (Value *)&protoFn_358);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keys_impl main body --------------
Function fn_941 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_958}}};


// --------- vals_impl --------------
Function fn_942;
Value *arityImpl_959(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_337(empty_list, rslt1, (Value *)&fn_377);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- vals_impl main body --------------
Function fn_942 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_959}}};


// --------- assoc_impl --------------
Function fn_943;
Value *arityImpl_960(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_943 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_960}}};


// --------- string-list_impl --------------
Function fn_944;

// --------- anon --------------
Function fn_965;
Value *arityImpl_966(List *closures, Value *arg2) {
List *arg3 = (List *)arg2;
Value *arg0 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *arg1 = arg3->head;
if (arg3->tail) arg3->tail->len = arg3->len - 1;
arg3 = arg3->tail;
Value *rslt4 = protoFnImpl_239(empty_list, arg0);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_52, varArgs5);
Value *rslt6 = arityImpl_186(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_239(empty_list, arg1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_186(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_396(empty_list, rslt4, rslt9);
incRef(rslt10);
dec_and_free(rslt6);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt10);
};


// --------- anon main body --------------
Function fn_965 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_966}}};

Value *arityImpl_961(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_368(empty_list, arg0);
Value *rslt2 = protoFnImpl_27(empty_list, rslt1);
Value *cond3;
Value *cond6;
Value *rslt7 = protoFnImpl_266(empty_list, (Value *)&_num_4, rslt1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
Value *cond8;
Value *rslt9 = protoFnImpl_222(empty_list, rslt2);
Value *rslt10 = protoFnImpl_200(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_76);
cond8 = var_76;
} else {
dec_and_free(rslt10);
incRef(var_75);
cond8 = var_75;
}
incRef(cond8);
cond6 = cond8;
dec_and_free(cond8);
} else {
dec_and_free(rslt7);
incRef(var_76);
cond6 = var_76;
}

if (isTrue(cond6)) {
dec_and_free(cond6);
List *arg13 = (List *)rslt2;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *rslt15 = protoFnImpl_337(empty_list, rslt1, (Value *)&fn_965);
List *varArgs16 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs16 = (List *)listCons((Value *)(Value *)&_str_57, varArgs16);
Value *rslt17 = arityImpl_186(empty_list, (Value *)varArgs16);
dec_and_free((Value *)varArgs16);
List *varArgs18 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs18 = (List *)listCons((Value *)(Value *)&_str_50, varArgs18);
Value *rslt19 = arityImpl_186(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
Value *rslt20 = arityImpl_719(empty_list, rslt15, rslt19);
List *varArgs21 = empty_list;
incRef((Value *)rslt20);
varArgs21 = (List *)listCons((Value *)rslt20, varArgs21);
Value *rslt22 = arityImpl_186(empty_list, (Value *)varArgs21);
dec_and_free((Value *)varArgs21);
Value *rslt23 = arityImpl_646(empty_list, (Value *)&fn_407, rslt22);
List *varArgs24 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs24 = (List *)listCons((Value *)(Value *)&_str_58, varArgs24);
Value *rslt25 = arityImpl_186(empty_list, (Value *)varArgs24);
dec_and_free((Value *)varArgs24);
List *varArgs26 = empty_list;
incRef((Value *)rslt25);
varArgs26 = (List *)listCons((Value *)rslt25, varArgs26);
incRef((Value *)rslt23);
varArgs26 = (List *)listCons((Value *)rslt23, varArgs26);
Value *rslt27 = arityImpl_186(empty_list, (Value *)varArgs26);
dec_and_free((Value *)varArgs26);
Value *rslt28 = arityImpl_706(empty_list, rslt17, rslt27);
incRef(rslt28);
cond3 = rslt28;
dec_and_free(rslt15);
dec_and_free(rslt27);
dec_and_free(rslt28);
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt22);
dec_and_free(rslt17);
dec_and_free(rslt25);
dec_and_free(rslt23);
} else {
dec_and_free(cond6);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_59, varArgs4);
Value *rslt5 = arityImpl_186(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
incRef(rslt5);
cond3 = rslt5;
dec_and_free(rslt5);
}
incRef(cond3);
dec_and_free(rslt1);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- string-list_impl main body --------------
Function fn_944 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_961}}};


// --------- seq_impl --------------
Function fn_945;
Value *arityImpl_967(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_424(empty_list, arg0, var_129);
return(rslt1);
};


// --------- seq_impl main body --------------
Function fn_945 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_967}}};


// --------- hash-seq_impl --------------
Function fn_946;
Value *arityImpl_968(List *closures, Value *arg0, Value *arg1) {

HashCollisionNode *node = (HashCollisionNode *)arg0;
List *seq = (List *)arg1;
for (int i = 0; i < node->count / 2; i++) {
   if (node->array[2 * i] != (Value *)0 && node->array[2 * i + 1] != (Value *)0) {
     List *pair = listCons(node->array[2 * i], listCons(node->array[2 * i + 1], empty_list));
     incRef(node->array[2 * i]);
     incRef(node->array[2 * i + 1]);
     seq = listCons((Value *)pair, seq);
   }
}
return((Value *)seq);
};


// --------- hash-seq_impl main body --------------
Function fn_946 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_968}}};


// --------- assoc*_impl --------------
Function fn_947;
Value *arityImpl_969(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

HashCollisionNode *node = (HashCollisionNode *)arg0;
Value *key = arg1;
Value *val = arg2;
int64_t hash = ((Number *)arg3)->numVal;
int shift = (int)((Number *)arg4)->numVal;
HashCollisionNode *newNode;
int itemCount = node->count / 2;

if(equal(sha1(node->array[0]), arg3)) {
   newNode = malloc_hashCollisionNode(itemCount + 1);
   for (int i = 0; i < itemCount; i++) {
      if (equal(node->array[2 * i], key)) {
         newNode->array[2 * i] = key;
         incRef(key);
         newNode->array[2 * i + 1] = val;
         incRef(val);
         newNode->count--;
      } else {
         newNode->array[2 * i] = node->array[2 * i];
         incRef(node->array[2 * i]);
         newNode->array[2 * i + 1] = node->array[2 * i + 1];
         incRef(node->array[2 * i + 1]);
      }
   }
   if (newNode->count != itemCount) {
      newNode->array[2 * itemCount] = key;
      incRef(key);
      newNode->array[2 * itemCount + 1] = val;
      incRef(val);
   }
   return((Value *)newNode);
} else {
   BitmapIndexedNode *bmi = &emptyBMI;
   Number newShift = {NumberType, -1, 0};

   bmi = (BitmapIndexedNode *)assoc((Value *)bmi, key, val, arg3, (Value *)&newShift);
   for (int i = 0; i < itemCount; i++) {
      bmi = (BitmapIndexedNode *)assoc((Value *)bmi, node->array[2 * i], node->array[2 * i + 1],
                                       sha1(node->array[i]), (Value *)&newShift);
   }
   return((Value *)bmi);
}
};


// --------- assoc*_impl main body --------------
Function fn_947 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_969}}};


// --------- get*_impl --------------
Function fn_948;
Value *arityImpl_970(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

HashCollisionNode *node = (HashCollisionNode *)arg0;
List *seq = (List *)arg1;
for (int i = 0; i < node->count / 2; i++) {
   if (node->array[2 * i] != (Value *)0 && equal(arg1, node->array[2 * i])) {
      if (node->array[2 * i + 1] != (Value *)0) {
        incRef(node->array[2 * i + 1]);
        return(node->array[2 * i + 1]);
      } else {
        incRef(arg2);
        return(arg2);
      }
   }
}
incRef(arg2);
return(arg2);
};


// --------- get*_impl main body --------------
Function fn_948 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_970}}};


// --------- hash-map --------------
Function fn_971;

// --------- anon --------------
Function fn_973;
Value *arityImpl_974(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_646(empty_list, (Value *)&protoFn_427, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_973 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_974}}};

Value *arityImpl_972(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_841(empty_list, arg0, (Value *)&_num_2);
Value *rslt3 = protoFnImpl_230(empty_list, rslt1, var_865, (Value *)&fn_973);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};

// --------- hash-map main body --------------
Function fn_971 = {FunctionType, -1, "hash-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_972}}};


// --------- m-get --------------
Function fn_976;

// --------- =*_impl --------------
Function fn_979;
Value *arityImpl_980(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_99(empty_list, arg0);
Value *rslt3 = arityImpl_99(empty_list, arg1);
Value *rslt4 = arityImpl_462(empty_list, rslt2, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};


// --------- =*_impl main body --------------
Function fn_979 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_980}}};

Value *protoImpl_981(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_978 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_981}}};

ReifiedVal reified_982 = {17, -1, 1, {(Value *)&fn_979}};
Value *arityImpl_977(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_448(empty_list, arg0, arg1, (Value *)&reified_982);
Value *cond4;
Value *rslt6 = arityImpl_462(empty_list, (Value *)&reified_982, rslt3);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef((Value *)&reified_522);
cond4 = (Value *)&reified_522;
} else {
dec_and_free(rslt6);
Value *rslt5 = protoImpl_599(empty_list, (Value *)&reified_602, rslt3);
incRef(rslt5);
cond4 = rslt5;
dec_and_free(rslt5);
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
return(cond4);
};


// --------- m-get main body --------------
Function fn_976 = {FunctionType, -1, "m-get", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_977}}};


// --------- merge-with --------------
Function fn_984;

// --------- anon --------------
Function fn_989;

// --------- anon --------------
Function fn_991;
Value *arityImpl_992(List *closures, Value *arg0, Value *arg3) {
Value * val16  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *arg4 = (List *)arg3;
Value *arg1 = arg4->head;
if (arg4->tail) arg4->tail->len = arg4->len - 1;
arg4 = arg4->tail;
Value *arg2 = arg4->head;
if (arg4->tail) arg4->tail->len = arg4->len - 1;
arg4 = arg4->tail;
Value *rslt5 = arityImpl_977(empty_list, arg0, arg1);
Value *rslt6 = protoFnImpl_27(empty_list, rslt5);
Value *cond7;
Value *cond8;
Value *rslt9 = protoImpl_601(empty_list, (Value *)&reified_602, rslt5);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
Value *cond10;
Value *rslt11 = protoFnImpl_222(empty_list, rslt6);
Value *rslt12 = protoFnImpl_200(empty_list, rslt11, (Value *)&_num_1);
dec_and_free(rslt11);

if (isTrue(rslt12)) {
dec_and_free(rslt12);
incRef(var_76);
cond10 = var_76;
} else {
dec_and_free(rslt12);
incRef(var_75);
cond10 = var_75;
}
incRef(cond10);
cond8 = cond10;
dec_and_free(cond10);
} else {
dec_and_free(rslt9);
incRef(var_76);
cond8 = var_76;
}

if (isTrue(cond8)) {
dec_and_free(cond8);
List *arg15 = (List *)rslt6;
Value *arg13 = arg15->head;
if (arg15->tail) arg15->tail->len = arg15->len - 1;
arg15 = arg15->tail;
Value *arg14 = (Value *) arg15;
Value *rslt20;
if((val16)->type != FunctionType) {
rslt20 = protoFnImpl_13(empty_list, val16, arg13, arg2);
} else {
FnArity *arity17 = findFnArity(val16, 2);
if(arity17 != (FnArity *)0 && !arity17->variadic) {
FnType2 *fn19 = (FnType2 *)arity17->fn;
rslt20 = fn19(arity17->closures, arg13, arg2);
} else if(arity17 != (FnArity *)0 && arity17->variadic) {
FnType1 *fn19 = (FnType1 *)arity17->fn;
List *varArgs18 = empty_list;
incRef(arg2);
varArgs18 = (List *)listCons(arg2, varArgs18);
incRef(arg13);
varArgs18 = (List *)listCons(arg13, varArgs18);
rslt20 = fn19(arity17->closures, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val16)->name);
  abort();
}
}
incRef(rslt20);
cond7 = rslt20;
dec_and_free(rslt20);
} else {
dec_and_free(cond8);
incRef(arg2);
cond7 = arg2;
}
Value *rslt21 = protoFnImpl_441(empty_list, arg0, arg1, cond7);
incRef(rslt21);
dec_and_free(rslt6);
dec_and_free(cond7);
dec_and_free(rslt5);
dec_and_free(rslt21);
return(rslt21);
};

Value *arityImpl_990(List *closures, Value *arg0, Value *arg1) {
Value * val4  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = protoFnImpl_368(empty_list, arg1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_992;
incRef((Value *)val4);
arity_3->closures = listCons((Value *)val4, (List *)arity_3->closures);
Function *fn_991 = malloc_function(1);
fn_991->type = FunctionType;
fn_991->name = "anon";
fn_991->arityCount = 1;
fn_991->arities[0] = arity_3;
Value *rslt5 = protoFnImpl_230(empty_list, rslt2, arg0, (Value *)fn_991);
incRef(rslt5);
dec_and_free((Value *)fn_991);
dec_and_free(rslt5);
dec_and_free(rslt2);
return(rslt5);
};

Value *arityImpl_985(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *) argsList;
Value *rslt3 = arityImpl_717(empty_list, arg2);
Value *cond4;
Value *cond5;

if (isTrue((Value *)&trueVal)) {
dec_and_free((Value *)&trueVal);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt3);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond5 = cond6;
dec_and_free(cond6);
} else {
dec_and_free((Value *)&trueVal);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg11 = (List *)rslt3;
Value *arg9 = arg11->head;
if (arg11->tail) arg11->tail->len = arg11->len - 1;
arg11 = arg11->tail;
Value *arg10 = (Value *) arg11;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = FnArityType;
arity_12->count = 2;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_990;
incRef((Value *)arg0);
arity_12->closures = listCons((Value *)arg0, (List *)arity_12->closures);
Function *fn_989 = malloc_function(1);
fn_989->type = FunctionType;
fn_989->name = "anon";
fn_989->arityCount = 1;
fn_989->arities[0] = arity_12;
Value *rslt13 = arityImpl_693(empty_list, arg2, arg1, (Value *)fn_989);
incRef(rslt13);
cond4 = rslt13;
dec_and_free(rslt13);
dec_and_free((Value *)fn_989);
} else {
dec_and_free(cond5);
incRef(arg1);
cond4 = arg1;
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
return(cond4);
};

// --------- merge-with main body --------------
Function fn_984 = {FunctionType, -1, "merge-with", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_985}}};


// --------- get-in --------------
Function fn_998;

// --------- anon --------------
Function fn_1004;

// --------- anon --------------
Function fn_1006;
Value *arityImpl_1007(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = protoFnImpl_306(empty_list, val1, arg0);
return(rslt2);
};

Value *arityImpl_1005(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val8  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = protoFnImpl_366(empty_list, val1);
Value *rslt6;
FnArity *arity3 = findFnArity((Value *)&fn_998, 2);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType2 *fn5 = (FnType2 *)arity3->fn;
rslt6 = fn5(arity3->closures, arg0, rslt2);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(rslt2);
varArgs4 = (List *)listCons(rslt2, varArgs4);
incRef(arg0);
varArgs4 = (List *)listCons(arg0, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_998)->name);
  abort();
}
FnArity *arity_7 = malloc_fnArity();
arity_7->type = FnArityType;
arity_7->count = 1;
arity_7->closures = empty_list;
arity_7->variadic = 0;
arity_7->fn = arityImpl_1007;
incRef((Value *)val8);
arity_7->closures = listCons((Value *)val8, (List *)arity_7->closures);
Function *fn_1006 = malloc_function(1);
fn_1006->type = FunctionType;
fn_1006->name = "anon";
fn_1006->arityCount = 1;
fn_1006->arities[0] = arity_7;
Value *rslt9 = protoFnImpl_275(empty_list, rslt6, (Value *)fn_1006);
incRef(rslt9);
dec_and_free(rslt6);
dec_and_free((Value *)fn_1006);
dec_and_free(rslt9);
dec_and_free(rslt2);
return(rslt9);
};

Value *arityImpl_999(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *cond6;
Value *rslt7 = protoFnImpl_222(empty_list, rslt2);
Value *rslt8 = protoFnImpl_200(empty_list, rslt7, (Value *)&_num_2);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_76);
cond6 = var_76;
} else {
dec_and_free(rslt8);
incRef(var_75);
cond6 = var_75;
}
incRef(cond6);
cond4 = cond6;
dec_and_free(cond6);
} else {
dec_and_free(rslt5);
incRef(var_76);
cond4 = var_76;
}

if (isTrue(cond4)) {
dec_and_free(cond4);
List *arg12 = (List *)rslt2;
Value *arg9 = arg12->head;
if (arg12->tail) arg12->tail->len = arg12->len - 1;
arg12 = arg12->tail;
Value *arg10 = arg12->head;
if (arg12->tail) arg12->tail->len = arg12->len - 1;
arg12 = arg12->tail;
Value *arg11 = (Value *) arg12;
Value *rslt13 = arityImpl_977(empty_list, arg0, arg9);
FnArity *arity_14 = malloc_fnArity();
arity_14->type = FnArityType;
arity_14->count = 1;
arity_14->closures = empty_list;
arity_14->variadic = 0;
arity_14->fn = arityImpl_1005;
incRef((Value *)rslt13);
arity_14->closures = listCons((Value *)rslt13, (List *)arity_14->closures);
incRef((Value *)arg1);
arity_14->closures = listCons((Value *)arg1, (List *)arity_14->closures);
Function *fn_1004 = malloc_function(1);
fn_1004->type = FunctionType;
fn_1004->name = "anon";
fn_1004->arityCount = 1;
fn_1004->arities[0] = arity_14;
Value *rslt15 = protoFnImpl_275(empty_list, rslt13, (Value *)fn_1004);
incRef(rslt15);
cond3 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt13);
dec_and_free((Value *)fn_1004);
} else {
dec_and_free(cond4);
Value *cond16;
Value *rslt17 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt17)) {
dec_and_free(rslt17);
Value *cond18;
Value *rslt19 = protoFnImpl_222(empty_list, rslt2);
Value *rslt20 = protoFnImpl_200(empty_list, rslt19, (Value *)&_num_1);
dec_and_free(rslt19);

if (isTrue(rslt20)) {
dec_and_free(rslt20);
incRef(var_76);
cond18 = var_76;
} else {
dec_and_free(rslt20);
incRef(var_75);
cond18 = var_75;
}
incRef(cond18);
cond16 = cond18;
dec_and_free(cond18);
} else {
dec_and_free(rslt17);
incRef(var_76);
cond16 = var_76;
}

if (isTrue(cond16)) {
dec_and_free(cond16);
List *arg23 = (List *)rslt2;
Value *arg21 = arg23->head;
if (arg23->tail) arg23->tail->len = arg23->len - 1;
arg23 = arg23->tail;
Value *arg22 = (Value *) arg23;
Value *rslt24 = arityImpl_977(empty_list, arg0, arg21);
incRef(rslt24);
cond3 = rslt24;
dec_and_free(rslt24);
} else {
dec_and_free(cond16);
incRef((Value *)&reified_522);
cond3 = (Value *)&reified_522;
}
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- get-in main body --------------
Function fn_998 = {FunctionType, -1, "get-in", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_999}}};


// --------- update-in --------------
Function fn_1009;
Value *arityImpl_1010(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_27(empty_list, arg1);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *cond7;
Value *rslt8 = protoFnImpl_222(empty_list, rslt3);
Value *rslt9 = protoFnImpl_200(empty_list, rslt8, (Value *)&_num_2);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(var_76);
cond7 = var_76;
} else {
dec_and_free(rslt9);
incRef(var_75);
cond7 = var_75;
}
incRef(cond7);
cond5 = cond7;
dec_and_free(cond7);
} else {
dec_and_free(rslt6);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg13 = (List *)rslt3;
Value *arg10 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *rslt14 = arityImpl_977(empty_list, arg0, arg10);
Value *rslt15 = protoFnImpl_27(empty_list, rslt14);
Value *cond16;
Value *cond17;
Value *rslt18 = protoImpl_601(empty_list, (Value *)&reified_602, rslt14);

if (isTrue(rslt18)) {
dec_and_free(rslt18);
Value *cond19;
Value *rslt20 = protoFnImpl_222(empty_list, rslt15);
Value *rslt21 = protoFnImpl_200(empty_list, rslt20, (Value *)&_num_1);
dec_and_free(rslt20);

if (isTrue(rslt21)) {
dec_and_free(rslt21);
incRef(var_76);
cond19 = var_76;
} else {
dec_and_free(rslt21);
incRef(var_75);
cond19 = var_75;
}
incRef(cond19);
cond17 = cond19;
dec_and_free(cond19);
} else {
dec_and_free(rslt18);
incRef(var_76);
cond17 = var_76;
}

if (isTrue(cond17)) {
dec_and_free(cond17);
List *arg24 = (List *)rslt15;
Value *arg22 = arg24->head;
if (arg24->tail) arg24->tail->len = arg24->len - 1;
arg24 = arg24->tail;
Value *arg23 = (Value *) arg24;
Value *rslt25 = protoFnImpl_366(empty_list, arg1);
Value *rslt26 = arityImpl_1010(closures, arg22, rslt25, arg2);
Value *rslt27 = protoFnImpl_441(empty_list, arg0, arg10, rslt26);
incRef(rslt27);
cond16 = rslt27;
dec_and_free(rslt26);
dec_and_free(rslt27);
dec_and_free(rslt25);
} else {
dec_and_free(cond17);
incRef(arg0);
cond16 = arg0;
}
incRef(cond16);
cond4 = cond16;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(cond16);
} else {
dec_and_free(cond5);
Value *cond28;
Value *rslt29 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt29)) {
dec_and_free(rslt29);
Value *cond30;
Value *rslt31 = protoFnImpl_222(empty_list, rslt3);
Value *rslt32 = protoFnImpl_200(empty_list, rslt31, (Value *)&_num_1);
dec_and_free(rslt31);

if (isTrue(rslt32)) {
dec_and_free(rslt32);
incRef(var_76);
cond30 = var_76;
} else {
dec_and_free(rslt32);
incRef(var_75);
cond30 = var_75;
}
incRef(cond30);
cond28 = cond30;
dec_and_free(cond30);
} else {
dec_and_free(rslt29);
incRef(var_76);
cond28 = var_76;
}

if (isTrue(cond28)) {
dec_and_free(cond28);
List *arg35 = (List *)rslt3;
Value *arg33 = arg35->head;
if (arg35->tail) arg35->tail->len = arg35->len - 1;
arg35 = arg35->tail;
Value *arg34 = (Value *) arg35;
Value *rslt36 = arityImpl_977(empty_list, arg0, arg33);
Value *rslt37 = protoFnImpl_27(empty_list, rslt36);
Value *cond38;
Value *cond39;
Value *rslt40 = protoImpl_601(empty_list, (Value *)&reified_602, rslt36);

if (isTrue(rslt40)) {
dec_and_free(rslt40);
Value *cond41;
Value *rslt42 = protoFnImpl_222(empty_list, rslt37);
Value *rslt43 = protoFnImpl_200(empty_list, rslt42, (Value *)&_num_1);
dec_and_free(rslt42);

if (isTrue(rslt43)) {
dec_and_free(rslt43);
incRef(var_76);
cond41 = var_76;
} else {
dec_and_free(rslt43);
incRef(var_75);
cond41 = var_75;
}
incRef(cond41);
cond39 = cond41;
dec_and_free(cond41);
} else {
dec_and_free(rslt40);
incRef(var_76);
cond39 = var_76;
}

if (isTrue(cond39)) {
dec_and_free(cond39);
List *arg46 = (List *)rslt37;
Value *arg44 = arg46->head;
if (arg46->tail) arg46->tail->len = arg46->len - 1;
arg46 = arg46->tail;
Value *arg45 = (Value *) arg46;
Value *rslt50;
if((arg2)->type != FunctionType) {
rslt50 = protoFnImpl_11(empty_list, arg2, arg44);
} else {
FnArity *arity47 = findFnArity(arg2, 1);
if(arity47 != (FnArity *)0 && !arity47->variadic) {
FnType1 *fn49 = (FnType1 *)arity47->fn;
rslt50 = fn49(arity47->closures, arg44);
} else if(arity47 != (FnArity *)0 && arity47->variadic) {
FnType1 *fn49 = (FnType1 *)arity47->fn;
List *varArgs48 = empty_list;
incRef(arg44);
varArgs48 = (List *)listCons(arg44, varArgs48);
rslt50 = fn49(arity47->closures, (Value *)varArgs48);
dec_and_free((Value *)varArgs48);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg2)->name);
  abort();
}
}
Value *rslt51 = protoFnImpl_441(empty_list, arg0, arg33, rslt50);
incRef(rslt51);
cond38 = rslt51;
dec_and_free(rslt50);
dec_and_free(rslt51);
} else {
dec_and_free(cond39);
incRef(arg0);
cond38 = arg0;
}
incRef(cond38);
cond4 = cond38;
dec_and_free(rslt37);
dec_and_free(cond38);
dec_and_free(rslt36);
} else {
dec_and_free(cond28);
incRef(arg0);
cond4 = arg0;
}
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
return(cond4);
};


// --------- update-in main body --------------
Function fn_1009 = {FunctionType, -1, "update-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_1010}}};


// --------- assoc-in --------------
Function fn_1022;
Value *arityImpl_1023(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_27(empty_list, arg1);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *cond7;
Value *rslt8 = protoFnImpl_222(empty_list, rslt3);
Value *rslt9 = protoFnImpl_200(empty_list, rslt8, (Value *)&_num_2);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(var_76);
cond7 = var_76;
} else {
dec_and_free(rslt9);
incRef(var_75);
cond7 = var_75;
}
incRef(cond7);
cond5 = cond7;
dec_and_free(cond7);
} else {
dec_and_free(rslt6);
incRef(var_76);
cond5 = var_76;
}

if (isTrue(cond5)) {
dec_and_free(cond5);
List *arg13 = (List *)rslt3;
Value *arg10 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg11 = arg13->head;
if (arg13->tail) arg13->tail->len = arg13->len - 1;
arg13 = arg13->tail;
Value *arg12 = (Value *) arg13;
Value *rslt14 = arityImpl_977(empty_list, arg0, arg10);
Value *rslt15 = protoFnImpl_27(empty_list, rslt14);
Value *cond16;
Value *cond22;
Value *rslt23 = protoImpl_601(empty_list, (Value *)&reified_602, rslt14);

if (isTrue(rslt23)) {
dec_and_free(rslt23);
Value *cond24;
Value *rslt25 = protoFnImpl_222(empty_list, rslt15);
Value *rslt26 = protoFnImpl_200(empty_list, rslt25, (Value *)&_num_1);
dec_and_free(rslt25);

if (isTrue(rslt26)) {
dec_and_free(rslt26);
incRef(var_76);
cond24 = var_76;
} else {
dec_and_free(rslt26);
incRef(var_75);
cond24 = var_75;
}
incRef(cond24);
cond22 = cond24;
dec_and_free(cond24);
} else {
dec_and_free(rslt23);
incRef(var_76);
cond22 = var_76;
}

if (isTrue(cond22)) {
dec_and_free(cond22);
List *arg29 = (List *)rslt15;
Value *arg27 = arg29->head;
if (arg29->tail) arg29->tail->len = arg29->len - 1;
arg29 = arg29->tail;
Value *arg28 = (Value *) arg29;
Value *rslt30 = protoFnImpl_366(empty_list, arg1);
Value *rslt31 = arityImpl_1023(closures, arg27, rslt30, arg2);
Value *rslt32 = protoFnImpl_441(empty_list, arg0, arg10, rslt31);
incRef(rslt32);
cond16 = rslt32;
dec_and_free(rslt31);
dec_and_free(rslt30);
dec_and_free(rslt32);
} else {
dec_and_free(cond22);
List *varArgs17 = empty_list;
Value *rslt18 = arityImpl_972(empty_list, (Value *)varArgs17);
dec_and_free((Value *)varArgs17);
Value *rslt19 = protoFnImpl_366(empty_list, arg1);
Value *rslt20 = arityImpl_1023(closures, rslt18, rslt19, arg2);
Value *rslt21 = protoFnImpl_441(empty_list, arg0, arg10, rslt20);
incRef(rslt21);
cond16 = rslt21;
dec_and_free(rslt20);
dec_and_free(rslt19);
dec_and_free(rslt18);
dec_and_free(rslt21);
}
incRef(cond16);
cond4 = cond16;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(cond16);
} else {
dec_and_free(cond5);
Value *cond33;
Value *rslt34 = protoFnImpl_266(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt34)) {
dec_and_free(rslt34);
Value *cond35;
Value *rslt36 = protoFnImpl_222(empty_list, rslt3);
Value *rslt37 = protoFnImpl_200(empty_list, rslt36, (Value *)&_num_1);
dec_and_free(rslt36);

if (isTrue(rslt37)) {
dec_and_free(rslt37);
incRef(var_76);
cond35 = var_76;
} else {
dec_and_free(rslt37);
incRef(var_75);
cond35 = var_75;
}
incRef(cond35);
cond33 = cond35;
dec_and_free(cond35);
} else {
dec_and_free(rslt34);
incRef(var_76);
cond33 = var_76;
}

if (isTrue(cond33)) {
dec_and_free(cond33);
List *arg40 = (List *)rslt3;
Value *arg38 = arg40->head;
if (arg40->tail) arg40->tail->len = arg40->len - 1;
arg40 = arg40->tail;
Value *arg39 = (Value *) arg40;
Value *rslt41 = protoFnImpl_441(empty_list, arg0, arg38, arg2);
incRef(rslt41);
cond4 = rslt41;
dec_and_free(rslt41);
} else {
dec_and_free(cond33);
incRef(arg0);
cond4 = arg0;
}
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
return(cond4);
};


// --------- assoc-in main body --------------
Function fn_1022 = {FunctionType, -1, "assoc-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_1023}}};

SubString _kw_2 = {5, -1, 6, 0, 0, ":bogus"};

// --------- sha1_impl --------------
Function fn_1032;
Value *arityImpl_1037(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

if (subStrVal->hash != (Number *)0) {
  incRef((Value *)subStrVal->hash);
  return((Value *)subStrVal->hash);
}
else {
  Sha1Initialise(&context);
  Sha1Update(&context, (void *)&subStrVal->type, 8);
  Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
  Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
  Number *hashVal = (Number *)numberValue(shaVal);
  subStrVal->hash = (Number *)hashVal;
  incRef((Value *)hashVal);
  return((Value *)hashVal);
}
};


// --------- sha1_impl main body --------------
Function fn_1032 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1037}}};


// --------- =*_impl --------------
Function fn_1033;
Value *arityImpl_1038(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_159(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_1033 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_1038}}};


// --------- string-list_impl --------------
Function fn_1034;
Value *arityImpl_1039(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_343(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_1034 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1039}}};


// --------- invoke_impl --------------
Function fn_1035;
Value *arityImpl_1040(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_448(empty_list, arg1, arg0, (Value *)&_kw_2);
return(rslt2);
};


// --------- invoke_impl main body --------------
Function fn_1035 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_1040}}};


// --------- name_impl --------------
Function fn_1036;
Value *arityImpl_1041(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_84(empty_list, arg0);
return(rslt1);
};


// --------- name_impl main body --------------
Function fn_1036 = {FunctionType, -1, "name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1041}}};


// --------- sha1_impl --------------
Function fn_1042;
Value *arityImpl_1048(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

if (subStrVal->hash != (Number *)0) {
  incRef((Value *)subStrVal->hash);
  return((Value *)subStrVal->hash);
}
else {
  Sha1Initialise(&context);
  Sha1Update(&context, (void *)&subStrVal->type, 8);
  Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
  Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
  Number *hashVal = (Number *)numberValue(shaVal);
  subStrVal->hash = (Number *)hashVal;
  incRef((Value *)hashVal);
  return((Value *)hashVal);
}
};


// --------- sha1_impl main body --------------
Function fn_1042 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1048}}};


// --------- =*_impl --------------
Function fn_1043;
Value *arityImpl_1049(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_159(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_1043 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_1049}}};


// --------- string-list_impl --------------
Function fn_1044;
Value *arityImpl_1050(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_343(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_186(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_1044 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1050}}};


// --------- type-args_impl --------------
Function fn_1045;
Value *arityImpl_1051(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_186(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- type-args_impl main body --------------
Function fn_1045 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1051}}};


// --------- invoke_impl --------------
Function fn_1046;
Value *arityImpl_1052(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_977(empty_list, arg1, arg0);
return(rslt2);
};


// --------- invoke_impl main body --------------
Function fn_1046 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_1052}}};


// --------- name_impl --------------
Function fn_1047;
Value *arityImpl_1053(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_84(empty_list, arg0);
return(rslt1);
};


// --------- name_impl main body --------------
Function fn_1047 = {FunctionType, -1, "name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1053}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_60 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_1054;
Value *arityImpl_1055(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)(Value *)&_str_60);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_60, varArgs1);
Value *rslt2 = arityImpl_822(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_93(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- keyword main body --------------
Function fn_1054 = {FunctionType, -1, "keyword", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1055}}};


// --------- string? --------------
Function fn_1057;
Value *arityImpl_1058(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_99(empty_list, arg0);
Value *rslt2 = arityImpl_462(empty_list, (Value *)&_num_1, rslt1);
Value *rslt3 = arityImpl_99(empty_list, arg0);
Value *rslt4 = arityImpl_462(empty_list, (Value *)&_num_6, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
Value *rslt6 = arityImpl_458(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt6);
};


// --------- string? main body --------------
Function fn_1057 = {FunctionType, -1, "string?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1058}}};


// --------- range* --------------
Function fn_1060;
Value *arityImpl_1061(List *closures, Value *arg0) {
Value *cond1;
Value *rslt5 = arityImpl_462(empty_list, (Value *)&_num_13, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_num_13);
varArgs6 = (List *)listCons((Value *)(Value *)&_num_13, varArgs6);
Value *rslt7 = arityImpl_186(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
incRef(rslt7);
cond1 = rslt7;
dec_and_free(rslt7);
} else {
dec_and_free(rslt5);
Value *rslt2 = arityImpl_754(empty_list, arg0);
Value *rslt3 = arityImpl_1061(closures, rslt2);
Value *rslt4 = arityImpl_132(empty_list, arg0, rslt3);
incRef(rslt4);
cond1 = rslt4;
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- range* main body --------------
Function fn_1060 = {FunctionType, -1, "range*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1061}}};


// --------- range --------------
Function fn_1063;
Value *arityImpl_1064(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_754(empty_list, arg0);
Value *rslt2 = arityImpl_1061(empty_list, rslt1);
Value *rslt3 = arityImpl_233(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- range main body --------------
Function fn_1063 = {FunctionType, -1, "range", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1064}}};


// --------- repeat --------------
Function fn_1066;

// --------- anon --------------
Function fn_1068;
Value *arityImpl_1069(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val1);
return(val1);
};

Value *arityImpl_1067(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = arityImpl_623(empty_list, arg0, (Value *)&_num_1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt7);
Value *rslt3 = arityImpl_754(empty_list, arg0);
Value *rslt4 = arityImpl_1061(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = FnArityType;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_1069;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_1068 = malloc_function(1);
fn_1068->type = FunctionType;
fn_1068->name = "anon";
fn_1068->arityCount = 1;
fn_1068->arities[0] = arity_5;
Value *rslt6 = arityImpl_716(empty_list, rslt4, (Value *)fn_1068);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free((Value *)fn_1068);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- repeat main body --------------
Function fn_1066 = {FunctionType, -1, "repeat", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_1067}}};


 int64_t sym_counter = 0;

// --------- get-sym-count --------------
Function fn_1071;
Value *arityImpl_1072(List *closures) {

  return numberValue(sym_counter);
};


// --------- get-sym-count main body --------------
Function fn_1071 = {FunctionType, -1, "get-sym-count", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_1072}}};


// --------- set-sym-count --------------
Function fn_1074;
Value *arityImpl_1075(List *closures, Value *arg0) {

  sym_counter = ((Number *)arg0)->numVal;
  return true;
};


// --------- set-sym-count main body --------------
Function fn_1074 = {FunctionType, -1, "set-sym-count", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1075}}};


// --------- new-sym-count --------------
Function fn_1077;
Value *arityImpl_1078(List *closures) {

 static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

 pthread_mutex_lock (&mutex);

 // store value before any other threads increment it further
 int64_t result = sym_counter;
 // only allow one thread to increment at a time
 ++sym_counter;

 pthread_mutex_unlock (&mutex);

 return numberValue(result);
};


// --------- new-sym-count main body --------------
Function fn_1077 = {FunctionType, -1, "new-sym-count", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_1078}}};


// --------- gensym --------------
Function fn_1080;
Value *arityImpl_1081(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_1078(empty_list);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_822(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_90(empty_list, rslt3);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- gensym main body --------------
Function fn_1080 = {FunctionType, -1, "gensym", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1081}}};

Value *get(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_420((List *)0, node, key, val, hash, shift));
}
Value *assoc(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_422((List *)0, node, key, val, hash, shift));
}
Value *valsEqual(List *x, Value *v1, Value *v2) {
  return(protoFnImpl_245(x, v1, v2));
}
Value *sha1(Value *v) {
  return(protoFnImpl_250((List *)0, v));
}
Value *hashSeq(Value *n, Value *s) {
  return(protoFnImpl_424((List *)0, n, s));
}
Value *count(Value *n) {
  return(protoFnImpl_222((List *)0, n));
}
Value *symbol_literals() {
List *syms = empty_list;
return((Value *)syms);
}

Value *number_literals() {
List *nums = empty_list;
List *numInfo;
numInfo = listCons(stringValue("_num_4"), empty_list);
numInfo = listCons(numberValue(4), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_14"), empty_list);
numInfo = listCons(numberValue(15), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_3"), empty_list);
numInfo = listCons(numberValue(3), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_11"), empty_list);
numInfo = listCons(numberValue(11), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_9"), empty_list);
numInfo = listCons(numberValue(9), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_13"), empty_list);
numInfo = listCons(numberValue(0), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_5"), empty_list);
numInfo = listCons(numberValue(5), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_10"), empty_list);
numInfo = listCons(numberValue(10), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_12"), empty_list);
numInfo = listCons(numberValue(12), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_1"), empty_list);
numInfo = listCons(numberValue(1), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_7"), empty_list);
numInfo = listCons(numberValue(7), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_6"), empty_list);
numInfo = listCons(numberValue(6), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_8"), empty_list);
numInfo = listCons(numberValue(8), numInfo);
nums = listCons((Value *)numInfo, nums);
numInfo = listCons(stringValue("_num_2"), empty_list);
numInfo = listCons(numberValue(2), numInfo);
nums = listCons((Value *)numInfo, nums);
return((Value *)nums);
}

Value *string_literals() {
List *strs = empty_list;
List *strInfo;
strInfo = listCons(stringValue("_str_59"), empty_list);
strInfo = listCons(stringValue("{}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_26"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t implCount; Value *defaultImpl; ProtoImpl impls[];} ProtoImpls;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_1"), empty_list);
strInfo = listCons(stringValue("Symbol"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_21"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; Number *hash; Value *source; char *buffer;} SubString;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_29"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int32_t bitmap; Value *array[];} BitmapIndexedNode;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_7"), empty_list);
strInfo = listCons(stringValue("String"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_44"), empty_list);
strInfo = listCons(stringValue("&"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_54"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_45"), empty_list);
strInfo = listCons(stringValue("<maybe "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_55"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_33"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_43"), empty_list);
strInfo = listCons(stringValue("<nothing>"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_32"), empty_list);
strInfo = listCons(stringValue("'<*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_52"), empty_list);
strInfo = listCons(stringValue(" "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_31"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int16_t count; Value *array[];} HashCollisionNode;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_5"), empty_list);
strInfo = listCons(stringValue("Number"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_19"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t numVal;} Number;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_16"), empty_list);
strInfo = listCons(stringValue("int64_t"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_27"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int implCount; Value* impls[];} ReifiedVal;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_11"), empty_list);
strInfo = listCons(stringValue("FnArity"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_40"), empty_list);
strInfo = listCons(stringValue("'get' not implemented for"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_34"), empty_list);
strInfo = listCons(stringValue("*** call to 'instance?' with unknown type parameter."), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_37"), empty_list);
strInfo = listCons(stringValue("*** 'wrap' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_18"), empty_list);
strInfo = listCons(stringValue("Value *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_50"), empty_list);
strInfo = listCons(stringValue(", "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_13"), empty_list);
strInfo = listCons(stringValue("char"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_9"), empty_list);
strInfo = listCons(stringValue("Function"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue("'serialize' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_2"), empty_list);
strInfo = listCons(stringValue("SubStr"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_38"), empty_list);
strInfo = listCons(stringValue("'name' not implemented for type "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_22"), empty_list);
strInfo = listCons(stringValue("typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_42"), empty_list);
strInfo = listCons(stringValue("nothing"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_47"), empty_list);
strInfo = listCons(stringValue("maybe-val"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
strInfo = listCons(stringValue(": "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_25"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; Value *implFn;} ProtoImpl;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_6"), empty_list);
strInfo = listCons(stringValue("BitmapIndexedNode"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_35"), empty_list);
strInfo = listCons(stringValue("'flat-map' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_8"), empty_list);
strInfo = listCons(stringValue("HashCollisionNode"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_53"), empty_list);
strInfo = listCons(stringValue("\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_48"), empty_list);
strInfo = listCons(stringValue("<Fn: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_23"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_24"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; char *name; int64_t arityCount; FnArity *arities[];} Function;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_36"), empty_list);
strInfo = listCons(stringValue("'duplicate' not implemented: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_46"), empty_list);
strInfo = listCons(stringValue(">"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_12"), empty_list);
strInfo = listCons(stringValue("void"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_49"), empty_list);
strInfo = listCons(stringValue("("), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_28"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_51"), empty_list);
strInfo = listCons(stringValue(")"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_10"), empty_list);
strInfo = listCons(stringValue("Opaque"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_17"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs;} Value;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_15"), empty_list);
strInfo = listCons(stringValue("int"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_60"), empty_list);
strInfo = listCons(stringValue(":"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_30"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; Value *array[32];} ArrayNode;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_0"), empty_list);
strInfo = listCons(stringValue("ArrayNode"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_3"), empty_list);
strInfo = listCons(stringValue("Keyword"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_58"), empty_list);
strInfo = listCons(stringValue("}"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_14"), empty_list);
strInfo = listCons(stringValue("char *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_4"), empty_list);
strInfo = listCons(stringValue("List"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_20"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int64_t len; char buffer[0];} String;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_56"), empty_list);
strInfo = listCons(stringValue("'nth' from empty seq"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_57"), empty_list);
strInfo = listCons(stringValue("{"), strInfo);
strs = listCons((Value *)strInfo, strs);
return((Value *)strs);
}

Value *keyword_literals() {
List *kws = empty_list;
List *kwInfo;
kwInfo = listCons(stringValue("_kw_2"), empty_list);
kwInfo = listCons(keywordValue(":bogus"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_1"), empty_list);
kwInfo = listCons(keywordValue(":k"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_0"), empty_list);
kwInfo = listCons(keywordValue(":m"), kwInfo);
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
impl = listCons(stringValue("(Value *)&protoFn_560"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".v"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_525;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_524"), protoInfo);
protoInfo = listCons(stringValue("Getter/.v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_540"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_471"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_273"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flatten"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_272;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_271"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flatten"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_668"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_763"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_794"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_203;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_202"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_676"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_550"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_644"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_904"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_869"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_939"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_767"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_798"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_481"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("comp*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_391;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_390"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/comp*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_677"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_978"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1033"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_768"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1043"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_799"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_254"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_483"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_243"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("=*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_242;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_241"), protoInfo);
protoInfo = listCons(stringValue("core/Eq/=*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_672"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("crush"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_386;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_385"), protoInfo);
protoInfo = listCons(stringValue("core/Crushable/crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_671"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_766"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_797"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("reduce"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_218;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_217"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/reduce"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_347"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("serialize"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_346;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_345"), protoInfo);
protoInfo = listCons(stringValue("core/Serializable/serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_666"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("traverse"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_381;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_380"), protoInfo);
protoInfo = listCons(stringValue("core/Traversable/traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_907"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_872"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_942"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("vals"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_433;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_432"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_683"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_554"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_487"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_333"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_332;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_331"), protoInfo);
protoInfo = listCons(stringValue("core/Functor/map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1032"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_761"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1042"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_792"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_252"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("sha1"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_248;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_247"), protoInfo);
protoInfo = listCons(stringValue("core/Hash/sha1"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1036"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1047"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_341"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_340;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_339"), protoInfo);
protoInfo = listCons(stringValue("core/Named/name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_287"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("duplicate"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_286;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_285"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/duplicate"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_911"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_876"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_946"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("hash-seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_418;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_417"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/hash-seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_546"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_642"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_531"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_477"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_304"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("apply*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_303;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_302"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_673"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_542"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_473"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_270"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flat-map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_269;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_268"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flat-map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_681"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_772"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_803"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_358;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_357"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_670"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_901"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_866"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_936"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_764"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_795"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("count"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_206;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_205"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/count"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_905"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_870"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_940"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_437"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_436;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_435"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_913"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_878"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_948"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_412;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_411"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/get*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_912"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_877"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_947"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_415;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_414"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/assoc*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_37"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_558"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_47"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_29"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_49"), impl);
impl = listCons(numberValue(9), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_35"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_41"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_45"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_43"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_31"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_33"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_51"), impl);
impl = listCons(numberValue(8), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_39"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_489"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("type-name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_4;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_3"), protoInfo);
protoInfo = listCons(stringValue("Getter/type-name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_906"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_871"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_941"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("keys"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_439;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_438"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1035"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_533"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1046"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_592"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_493"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("invoke"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_1;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_0"), protoInfo);
protoInfo = listCons(stringValue("Function/invoke"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_674"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_544"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_475"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_301"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("wrap"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_300;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_299"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/wrap"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_535"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_594"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_264"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("instance?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_263;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_262"), protoInfo);
protoInfo = listCons(stringValue("core/Type/instance?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_667"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_902"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_867"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_937"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_762"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_793"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_215;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_214"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extend"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_283;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_282"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extend"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_684"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_556"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_774"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1045"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_256"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_491"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("type-args"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_7;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_6"), protoInfo);
protoInfo = listCons(stringValue("Getter/type-args"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_679"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_910"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_875"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_945"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_770"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_801"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_355;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_354"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_253"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_198"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("<*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_197;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_196"), protoInfo);
protoInfo = listCons(stringValue("core/Ord/<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_680"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_771"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_802"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("m-first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_361;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_360"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/m-first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("destruct"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_212;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_211"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/destruct"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("dissoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_430;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_429"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/dissoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_678"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_365"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_364;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_363"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extract"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_289;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_288"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extract"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_669"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_765"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_796"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("conj"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_209;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_208"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/conj"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_682"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_773"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_804"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("rest"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_352;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_351"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_908"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_873"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_943"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_427;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_426"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_675"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_548"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_643"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_903"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_868"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_938"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_590"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_479"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("zero"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_394;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_393"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_726"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_552"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_645"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_909"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1034"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_874"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_944"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_769"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_1044"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_800"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_255"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_485"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_237"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("string-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_236;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_235"), protoInfo);
protoInfo = listCons(stringValue("core/Stringable/string-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
return((Value *)protos);
}

Value *static_fns() {
List *staticFns = empty_list;
List *fnInfo;
List *arityInfo;
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("protoImpl_511"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_483"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_775"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_761"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_708"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_678"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_693"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_671"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_78"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_77"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_121"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_120"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_968"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_946"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_383"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_381"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_420"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_412"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_349"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_346"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_99"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_98"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("protoImpl_584"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_558"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_751"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_749"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_750"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_748"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_424"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_418"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_496"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_471"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_661"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_660"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_448"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_436"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(5), empty_list);
arityInfo = listCons(stringValue("arityImpl_1055"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1054"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_515"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_487"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_652"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_651"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_620"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_619"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_233"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_232"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_504"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_479"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_230"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_218"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1075"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1074"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_900"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_878"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_509"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_481"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_922"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_905"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_891"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_874"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_640"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_639"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_919"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_918"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_578"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_552"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_441"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_427"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_739"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_53"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_15"), arityInfo);
arityInfo = listCons(numberValue(4), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_13"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_17"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_9"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_21"), arityInfo);
arityInfo = listCons(numberValue(7), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_19"), arityInfo);
arityInfo = listCons(numberValue(6), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_23"), arityInfo);
arityInfo = listCons(numberValue(8), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_11"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_1"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_422"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_415"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_926"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_909"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_785"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_768"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_888"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_871"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_44"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_43"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_38"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_37"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_30"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_29"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_897"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_875"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_899"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_877"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoImpl_599"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_592"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_818"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_802"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_716"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_683"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_925"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_908"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_96"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_95"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_624"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_623"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_622"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_957"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_940"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_647"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_643"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_958"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_941"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_162"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_161"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_807"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_794"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_1050"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1044"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_692"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_670"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_450"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_439"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_889"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_872"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_124"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_123"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1010"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1009"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_147"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_146"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1078"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1077"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_156"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_155"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_781"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_767"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_1041"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1036"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_275"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_269"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_966"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_965"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_226"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_212"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_705"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_675"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_746"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_744"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_745"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_743"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_503"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_480"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_497"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_474"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_935"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_913"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_841"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_840"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_815"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_799"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_778"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_764"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_514"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_488"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_537"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_532"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_628"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_627"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_626"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_923"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_906"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_32"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_31"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_280"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_272"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_388"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_386"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_834"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_833"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_324"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_322"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_396"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_391"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_52"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_51"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_337"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_332"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_981"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_978"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_445"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_433"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_527"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_525"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_135"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_134"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_192"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_191"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_741"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_740"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_222"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_206"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_916"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_903"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_719"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_718"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_266"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_263"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_587"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_536"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_138"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_137"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_370"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_358"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_608"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_606"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_607"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_605"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_112"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_111"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_519"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_491"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_844"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_843"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_717"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_684"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_1051"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1045"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_934"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_912"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_398"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_394"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_316"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_303"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_596"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_591"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_500"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_475"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_961"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_944"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("protoImpl_574"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_548"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_115"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_114"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_896"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_895"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1048"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1042"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_84"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_83"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_822"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_821"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_588"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_535"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_977"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_976"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_691"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_669"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_924"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_907"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_186"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_185"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_949"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_936"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1072"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1071"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_707"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_677"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_700"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_673"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_520"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_494"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_320"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_319"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_50"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_49"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_171"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_170"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_458"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_457"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_456"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_709"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_679"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_320"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_298"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_658"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_657"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_954"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_953"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_405"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_404"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_403"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_510"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_484"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_819"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_803"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_739"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_738"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_970"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_948"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_704"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_674"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_34"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_33"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_710"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_680"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_950"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_937"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_250"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_248"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_980"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_979"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_985"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_984"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_87"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_86"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_495"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_472"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_566"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_545"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("protoImpl_597"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_590"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_150"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_149"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_879"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_866"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_501"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_478"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_366"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_352"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_882"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_869"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_653"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_645"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_788"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_771"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_463"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_461"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_462"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_460"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_601"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_594"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_25"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_4"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_648"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_644"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_512"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_486"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_498"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_473"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoImpl_567"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_544"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_972"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_971"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_200"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_197"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_600"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_595"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_183"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_182"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_886"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_885"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_921"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_920"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_810"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_797"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_81"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_80"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1052"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1046"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_969"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_947"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_637"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_636"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_959"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_942"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_409"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_408"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_407"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_690"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_668"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1038"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1033"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_141"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_140"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_565"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_542"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_127"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_126"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_714"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_681"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_786"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_769"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_837"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_838"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_836"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_931"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_930"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_697"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_672"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_951"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_938"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_956"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_955"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_932"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_910"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_259"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_254"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_805"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_792"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_586"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_560"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("protoImpl_513"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_485"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_401"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_400"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1064"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1063"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_974"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_973"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_754"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_753"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_806"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_793"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_820"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_804"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_153"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_152"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_732"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_731"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1067"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1066"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_576"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_550"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_257"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_252"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_572"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_546"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_631"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_630"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_1039"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1034"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_258"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_253"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_343"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_340"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_655"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_654"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_727"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_726"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_27"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_7"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_598"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_593"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_40"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_39"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_168"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_167"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_368"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_355"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_790"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_773"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_689"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_667"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_165"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_164"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_780"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_766"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_239"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_236"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_575"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_551"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_46"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_45"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("protoImpl_517"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_489"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_375"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_364"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_530"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_470"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_828"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_827"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_224"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_209"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_759"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_757"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_758"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_756"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_102"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_101"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_917"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_904"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_118"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_117"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_516"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_490"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_189"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_188"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_521"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_493"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_685"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_666"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(7), empty_list);
arityInfo = listCons(stringValue("arityImpl_1081"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1080"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_505"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_482"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_777"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_763"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_378"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_377"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_372"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_361"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_180"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_179"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(7), empty_list);
arityInfo = listCons(stringValue("arityImpl_90"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_89"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_715"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_682"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_539"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_534"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_291"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_283"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_729"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_728"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_583"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_559"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_296"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_289"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1058"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1057"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_967"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_945"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_131"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_132"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_130"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1037"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1032"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_887"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_870"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_279"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_278"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_779"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_765"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1049"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1043"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_776"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_762"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_499"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_476"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_228"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_215"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_816"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_800"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_880"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_867"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_811"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_798"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_159"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_158"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_109"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_108"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_789"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_772"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_580"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_554"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(5), empty_list);
arityInfo = listCons(stringValue("arityImpl_93"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_92"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_36"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_35"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_791"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_774"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_884"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_883"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_706"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_676"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_260"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_255"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_960"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_943"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_809"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_796"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_42"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_41"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_735"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_734"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_220"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_203"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_177"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_176"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_1053"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1047"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_817"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_801"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_518"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_492"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_443"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_430"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_1061"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1060"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_144"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_143"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_502"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_477"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_898"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_876"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_860"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_859"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_582"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_556"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_174"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_173"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_577"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_553"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_466"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_465"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_530"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_533"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_306"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_300"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_890"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_873"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_454"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_453"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_452"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_573"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_549"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1040"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1035"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1023"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1022"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_914"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_901"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_48"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_47"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_294"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_286"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_952"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_939"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_808"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_795"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_261"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_256"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_563"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_540"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_999"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_998"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_857"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_856"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_538"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_531"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_915"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_902"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_646"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_642"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_848"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_847"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_846"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_787"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_770"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_881"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_868"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_245"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_242"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_933"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_911"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_106"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_105"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_104"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
return((Value *)staticFns);
}

Value *defined_syms() {
List *defSyms = empty_list;
List *symInfo;
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_26"), symInfo);
symInfo = listCons(stringValue("String _str_26"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpls"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_352"), symInfo);
symInfo = listCons(stringValue("Function protoFn_352"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_947"), symInfo);
symInfo = listCons(stringValue("Function fn_947"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(16), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_602"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_602"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_355"), symInfo);
symInfo = listCons(stringValue("Function protoFn_355"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_300"), symInfo);
symInfo = listCons(stringValue("Function protoFn_300"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_731"), symInfo);
symInfo = listCons(stringValue("Function fn_731"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_377"), symInfo);
symInfo = listCons(stringValue("Function fn_377"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("second"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_30"), symInfo);
symInfo = listCons(stringValue("String _str_30"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ArrayNodeVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_945"), symInfo);
symInfo = listCons(stringValue("Function fn_945"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_12"), symInfo);
symInfo = listCons(stringValue("String _str_12"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("VoidT"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_728"), symInfo);
symInfo = listCons(stringValue("Function fn_728"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("prn"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_460"), symInfo);
symInfo = listCons(stringValue("Function fn_460"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_984"), symInfo);
symInfo = listCons(stringValue("Function fn_984"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_657"), symInfo);
symInfo = listCons(stringValue("Function fn_657"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_622"), symInfo);
symInfo = listCons(stringValue("Function fn_622"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_134"), symInfo);
symInfo = listCons(stringValue("Function fn_134"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_253"), symInfo);
symInfo = listCons(stringValue("Function fn_253"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_80"), symInfo);
symInfo = listCons(stringValue("Function fn_80"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("standard-output"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1009"), symInfo);
symInfo = listCons(stringValue("Function fn_1009"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_412"), symInfo);
symInfo = listCons(stringValue("Function protoFn_412"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_11"), symInfo);
symInfo = listCons(stringValue("Number _num_11"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ArrayNode"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_427"), symInfo);
symInfo = listCons(stringValue("Function protoFn_427"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_7"), symInfo);
symInfo = listCons(stringValue("Number _num_7"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_998"), symInfo);
symInfo = listCons(stringValue("Function fn_998"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_269"), symInfo);
symInfo = listCons(stringValue("Function protoFn_269"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_740"), symInfo);
symInfo = listCons(stringValue("Function fn_740"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("inc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_283"), symInfo);
symInfo = listCons(stringValue("Function protoFn_283"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_612"), symInfo);
symInfo = listCons(stringValue("Function fn_612"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("recur"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_673"), symInfo);
symInfo = listCons(stringValue("Function fn_673"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1071"), symInfo);
symInfo = listCons(stringValue("Function fn_1071"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-sym-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_654"), symInfo);
symInfo = listCons(stringValue("Function fn_654"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-concat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_14"), symInfo);
symInfo = listCons(stringValue("String _str_14"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_391"), symInfo);
symInfo = listCons(stringValue("Function protoFn_391"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_170"), symInfo);
symInfo = listCons(stringValue("Function fn_170"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("slurp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_753"), symInfo);
symInfo = listCons(stringValue("Function fn_753"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_415"), symInfo);
symInfo = listCons(stringValue("Function protoFn_415"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_865"), symInfo);
symInfo = listCons(stringValue("Value *var_865;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("emptyBMI"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_802"), symInfo);
symInfo = listCons(stringValue("Function fn_802"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m-first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_358"), symInfo);
symInfo = listCons(stringValue("Function protoFn_358"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_17"), symInfo);
symInfo = listCons(stringValue("String _str_17"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_95"), symInfo);
symInfo = listCons(stringValue("Function fn_95"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("abort"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_971"), symInfo);
symInfo = listCons(stringValue("Function fn_971"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(14), empty_list);
symInfo = listCons(stringValue("var_470"), symInfo);
symInfo = listCons(stringValue("Value *var_470"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe-val"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_836"), symInfo);
symInfo = listCons(stringValue("Function fn_836"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_340"), symInfo);
symInfo = listCons(stringValue("Function protoFn_340"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_804"), symInfo);
symInfo = listCons(stringValue("Function fn_804"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_83"), symInfo);
symInfo = listCons(stringValue("Function fn_83"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_27"), symInfo);
symInfo = listCons(stringValue("String _str_27"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ReifiedVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_394"), symInfo);
symInfo = listCons(stringValue("Function protoFn_394"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_242"), symInfo);
symInfo = listCons(stringValue("Function protoFn_242"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_943"), symInfo);
symInfo = listCons(stringValue("Function fn_943"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_203"), symInfo);
symInfo = listCons(stringValue("Function protoFn_203"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_92"), symInfo);
symInfo = listCons(stringValue("Function fn_92"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("new-keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_13"), symInfo);
symInfo = listCons(stringValue("String _str_13"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int8"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_561"), symInfo);
symInfo = listCons(stringValue("Function fn_561"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_6"), symInfo);
symInfo = listCons(stringValue("Number _num_6"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("SubStr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1042"), symInfo);
symInfo = listCons(stringValue("Function fn_1042"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("sha1_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_152"), symInfo);
symInfo = listCons(stringValue("Function fn_152"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_143"), symInfo);
symInfo = listCons(stringValue("Function fn_143"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cdr"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_155"), symInfo);
symInfo = listCons(stringValue("Function fn_155"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_185"), symInfo);
symInfo = listCons(stringValue("Function fn_185"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_7"), symInfo);
symInfo = listCons(stringValue("Function protoFn_7"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-args"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_456"), symInfo);
symInfo = listCons(stringValue("Function fn_456"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("or"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_158"), symInfo);
symInfo = listCons(stringValue("Function fn_158"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symkey="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_206"), symInfo);
symInfo = listCons(stringValue("Function protoFn_206"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1074"), symInfo);
symInfo = listCons(stringValue("Function fn_1074"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("set-sym-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_149"), symInfo);
symInfo = listCons(stringValue("Function fn_149"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_5"), symInfo);
symInfo = listCons(stringValue("Number _num_5"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_626"), symInfo);
symInfo = listCons(stringValue("Function fn_626"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m<"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_19"), symInfo);
symInfo = listCons(stringValue("String _str_19"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("NumberVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_718"), symInfo);
symInfo = listCons(stringValue("Function fn_718"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1080"), symInfo);
symInfo = listCons(stringValue("Function fn_1080"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("gensym"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1043"), symInfo);
symInfo = listCons(stringValue("Function fn_1043"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_98"), symInfo);
symInfo = listCons(stringValue("Function fn_98"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-type"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_938"), symInfo);
symInfo = listCons(stringValue("Function fn_938"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_319"), symInfo);
symInfo = listCons(stringValue("Function fn_319"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comprehend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_75"), symInfo);
symInfo = listCons(stringValue("Value *var_75;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("true"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_263"), symInfo);
symInfo = listCons(stringValue("Function protoFn_263"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_179"), symInfo);
symInfo = listCons(stringValue("Function fn_179"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("filter"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_4"), symInfo);
symInfo = listCons(stringValue("Number _num_4"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("List"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_21"), symInfo);
symInfo = listCons(stringValue("String _str_21"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("SubStringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_683"), symInfo);
symInfo = listCons(stringValue("Function fn_683"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_236"), symInfo);
symInfo = listCons(stringValue("Function protoFn_236"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_161"), symInfo);
symInfo = listCons(stringValue("Function fn_161"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-malloc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_605"), symInfo);
symInfo = listCons(stringValue("Function fn_605"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_23"), symInfo);
symInfo = listCons(stringValue("String _str_23"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArityVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_76"), symInfo);
symInfo = listCons(stringValue("Value *var_76;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("false"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_303"), symInfo);
symInfo = listCons(stringValue("Function protoFn_303"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_209"), symInfo);
symInfo = listCons(stringValue("Function protoFn_209"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_2"), symInfo);
symInfo = listCons(stringValue("Number _num_2"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Number"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_212"), symInfo);
symInfo = listCons(stringValue("Function protoFn_212"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("destruct"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_942"), symInfo);
symInfo = listCons(stringValue("Function fn_942"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_4"), symInfo);
symInfo = listCons(stringValue("Function protoFn_4"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_642"), symInfo);
symInfo = listCons(stringValue("Function fn_642"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_123"), symInfo);
symInfo = listCons(stringValue("Function fn_123"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("mult-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1066"), symInfo);
symInfo = listCons(stringValue("Function fn_1066"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("repeat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_346"), symInfo);
symInfo = listCons(stringValue("Function protoFn_346"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_101"), symInfo);
symInfo = listCons(stringValue("Function fn_101"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_176"), symInfo);
symInfo = listCons(stringValue("Function fn_176"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("escape-chars"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_430"), symInfo);
symInfo = listCons(stringValue("Function protoFn_430"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dissoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_948"), symInfo);
symInfo = listCons(stringValue("Function fn_948"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_332"), symInfo);
symInfo = listCons(stringValue("Function protoFn_332"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_636"), symInfo);
symInfo = listCons(stringValue("Function fn_636"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_286"), symInfo);
symInfo = listCons(stringValue("Function protoFn_286"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("duplicate"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_120"), symInfo);
symInfo = listCons(stringValue("Function fn_120"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subtract-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_22"), symInfo);
symInfo = listCons(stringValue("String _str_22"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ListVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_117"), symInfo);
symInfo = listCons(stringValue("Function fn_117"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("add-numbers"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1022"), symInfo);
symInfo = listCons(stringValue("Function fn_1022"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_734"), symInfo);
symInfo = listCons(stringValue("Function fn_734"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1063"), symInfo);
symInfo = listCons(stringValue("Function fn_1063"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_361"), symInfo);
symInfo = listCons(stringValue("Function protoFn_361"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m-first"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_29"), symInfo);
symInfo = listCons(stringValue("String _str_29"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("BitmapIndexedVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_77"), symInfo);
symInfo = listCons(stringValue("Function fn_77"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("output-to-file"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_541"), symInfo);
symInfo = listCons(stringValue("Function fn_541"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_465"), symInfo);
symInfo = listCons(stringValue("Function fn_465"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partial"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_16"), symInfo);
symInfo = listCons(stringValue("String _str_16"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int64"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_418"), symInfo);
symInfo = listCons(stringValue("Function protoFn_418"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_803"), symInfo);
symInfo = listCons(stringValue("Function fn_803"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_10"), symInfo);
symInfo = listCons(stringValue("Number _num_10"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("BitmapIndexedNode"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_796"), symInfo);
symInfo = listCons(stringValue("Function fn_796"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_738"), symInfo);
symInfo = listCons(stringValue("Function fn_738"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print-err"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_86"), symInfo);
symInfo = listCons(stringValue("Function fn_86"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("char-code"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_1"), symInfo);
symInfo = listCons(stringValue("Function protoFn_1"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_188"), symInfo);
symInfo = listCons(stringValue("Function fn_188"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_215"), symInfo);
symInfo = listCons(stringValue("Function protoFn_215"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_840"), symInfo);
symInfo = listCons(stringValue("Function fn_840"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_31"), symInfo);
symInfo = listCons(stringValue("String _str_31"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("HashCollisionVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_936"), symInfo);
symInfo = listCons(stringValue("Function fn_936"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_407"), symInfo);
symInfo = listCons(stringValue("Function fn_407"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_167"), symInfo);
symInfo = listCons(stringValue("Function fn_167"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr-err*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_939"), symInfo);
symInfo = listCons(stringValue("Function fn_939"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("comp*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_20"), symInfo);
symInfo = listCons(stringValue("String _str_20"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("StringVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_941"), symInfo);
symInfo = listCons(stringValue("Function fn_941"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_595"), symInfo);
symInfo = listCons(stringValue("Function fn_595"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_639"), symInfo);
symInfo = listCons(stringValue("Function fn_639"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1068"), symInfo);
symInfo = listCons(stringValue("Function fn_1068"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_846"), symInfo);
symInfo = listCons(stringValue("Function fn_846"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_1"), symInfo);
symInfo = listCons(stringValue("Number _num_1"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("String"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_104"), symInfo);
symInfo = listCons(stringValue("Function fn_104"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("subs"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_619"), symInfo);
symInfo = listCons(stringValue("Function fn_619"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("some"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_15"), symInfo);
symInfo = listCons(stringValue("String _str_15"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Int32"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_452"), symInfo);
symInfo = listCons(stringValue("Function fn_452"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("and"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_12"), symInfo);
symInfo = listCons(stringValue("Number _num_12"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("HashCollisionNode"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_130"), symInfo);
symInfo = listCons(stringValue("Function fn_130"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("cons"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_173"), symInfo);
symInfo = listCons(stringValue("Function fn_173"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_25"), symInfo);
symInfo = listCons(stringValue("String _str_25"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ProtoImpl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_403"), symInfo);
symInfo = listCons(stringValue("Function fn_403"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply-to"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_140"), symInfo);
symInfo = listCons(stringValue("Function fn_140"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("car"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_856"), symInfo);
symInfo = listCons(stringValue("Function fn_856"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("last"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_289"), symInfo);
symInfo = listCons(stringValue("Function protoFn_289"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extract"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1057"), symInfo);
symInfo = listCons(stringValue("Function fn_1057"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_756"), symInfo);
symInfo = listCons(stringValue("Function fn_756"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("-"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_126"), symInfo);
symInfo = listCons(stringValue("Function fn_126"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rem"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_197"), symInfo);
symInfo = listCons(stringValue("Function protoFn_197"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(13), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_522"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_522"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("nothing"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_146"), symInfo);
symInfo = listCons(stringValue("Function fn_146"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("fn-name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_386"), symInfo);
symInfo = listCons(stringValue("Function protoFn_386"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_381"), symInfo);
symInfo = listCons(stringValue("Function protoFn_381"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_111"), symInfo);
symInfo = listCons(stringValue("Function fn_111"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_559"), symInfo);
symInfo = listCons(stringValue("Function fn_559"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_748"), symInfo);
symInfo = listCons(stringValue("Function fn_748"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1046"), symInfo);
symInfo = listCons(stringValue("Function fn_1046"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_433"), symInfo);
symInfo = listCons(stringValue("Function protoFn_433"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_743"), symInfo);
symInfo = listCons(stringValue("Function fn_743"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1054"), symInfo);
symInfo = listCons(stringValue("Function fn_1054"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_89"), symInfo);
symInfo = listCons(stringValue("Function fn_89"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_28"), symInfo);
symInfo = listCons(stringValue("String _str_28"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("OpaqueVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_114"), symInfo);
symInfo = listCons(stringValue("Function fn_114"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-less-than"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_191"), symInfo);
symInfo = listCons(stringValue("Function fn_191"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_797"), symInfo);
symInfo = listCons(stringValue("Function fn_797"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_248"), symInfo);
symInfo = listCons(stringValue("Function protoFn_248"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("sha1"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_859"), symInfo);
symInfo = listCons(stringValue("Function fn_859"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_940"), symInfo);
symInfo = listCons(stringValue("Function fn_940"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_3"), symInfo);
symInfo = listCons(stringValue("Number _num_3"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Function"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_182"), symInfo);
symInfo = listCons(stringValue("Function fn_182"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("pr*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_24"), symInfo);
symInfo = listCons(stringValue("String _str_24"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FunctionVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_821"), symInfo);
symInfo = listCons(stringValue("Function fn_821"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_666"), symInfo);
symInfo = listCons(stringValue("Function fn_666"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_218"), symInfo);
symInfo = listCons(stringValue("Function protoFn_218"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_9"), symInfo);
symInfo = listCons(stringValue("Number _num_9"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Opaque"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_678"), symInfo);
symInfo = listCons(stringValue("Function fn_678"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_18"), symInfo);
symInfo = listCons(stringValue("String _str_18"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Value*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_827"), symInfo);
symInfo = listCons(stringValue("Function fn_827"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1077"), symInfo);
symInfo = listCons(stringValue("Function fn_1077"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("new-sym-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_137"), symInfo);
symInfo = listCons(stringValue("Function fn_137"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_272"), symInfo);
symInfo = listCons(stringValue("Function protoFn_272"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_232"), symInfo);
symInfo = listCons(stringValue("Function fn_232"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_436"), symInfo);
symInfo = listCons(stringValue("Function protoFn_436"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_660"), symInfo);
symInfo = listCons(stringValue("Function fn_660"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_794"), symInfo);
symInfo = listCons(stringValue("Function fn_794"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1060"), symInfo);
symInfo = listCons(stringValue("Function fn_1060"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_400"), symInfo);
symInfo = listCons(stringValue("Function fn_400"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_937"), symInfo);
symInfo = listCons(stringValue("Function fn_937"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_108"), symInfo);
symInfo = listCons(stringValue("Function fn_108"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number-str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1045"), symInfo);
symInfo = listCons(stringValue("Function fn_1045"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-args_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_833"), symInfo);
symInfo = listCons(stringValue("Function fn_833"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("drop"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1044"), symInfo);
symInfo = listCons(stringValue("Function fn_1044"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_946"), symInfo);
symInfo = listCons(stringValue("Function fn_946"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-seq_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_16"), symInfo);
symInfo = listCons(stringValue(""), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ValueType"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_843"), symInfo);
symInfo = listCons(stringValue("Function fn_843"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("partition-all"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_129"), symInfo);
symInfo = listCons(stringValue("Value *var_129;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_674"), symInfo);
symInfo = listCons(stringValue("Function fn_674"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_8"), symInfo);
symInfo = listCons(stringValue("Number _num_8"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_630"), symInfo);
symInfo = listCons(stringValue("Function fn_630"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1047"), symInfo);
symInfo = listCons(stringValue("Function fn_1047"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_976"), symInfo);
symInfo = listCons(stringValue("Function fn_976"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m-get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_439"), symInfo);
symInfo = listCons(stringValue("Function protoFn_439"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_364"), symInfo);
symInfo = listCons(stringValue("Function protoFn_364"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_525"), symInfo);
symInfo = listCons(stringValue("Function protoFn_525"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue(".v"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_164"), symInfo);
symInfo = listCons(stringValue("Function fn_164"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str-append"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_672"), symInfo);
symInfo = listCons(stringValue("Function fn_672"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
return((Value *)defSyms);
}

Value *types() {
List *types = empty_list;
List *typeInfo;
typeInfo = listCons(numberValue(17), empty_list);
typeInfo = listCons(symbolValue("17"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(11), empty_list);
typeInfo = listCons(symbolValue("ArrayNode"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(7), empty_list);
typeInfo = listCons(symbolValue("Symbol"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(15), empty_list);
typeInfo = listCons(symbolValue("maybe-val"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(6), empty_list);
typeInfo = listCons(symbolValue("SubStr"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(5), empty_list);
typeInfo = listCons(symbolValue("Keyword"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(4), empty_list);
typeInfo = listCons(symbolValue("List"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(2), empty_list);
typeInfo = listCons(symbolValue("Number"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(10), empty_list);
typeInfo = listCons(symbolValue("BitmapIndexedNode"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(1), empty_list);
typeInfo = listCons(symbolValue("String"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(12), empty_list);
typeInfo = listCons(symbolValue("HashCollisionNode"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(14), empty_list);
typeInfo = listCons(symbolValue("14"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(3), empty_list);
typeInfo = listCons(symbolValue("Function"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(16), empty_list);
typeInfo = listCons(symbolValue("16"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(9), empty_list);
typeInfo = listCons(symbolValue("Opaque"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(8), empty_list);
typeInfo = listCons(symbolValue("FnArity"), typeInfo);
types = listCons((Value *)typeInfo, types);
typeInfo = listCons(numberValue(13), empty_list);
typeInfo = listCons(symbolValue("13"), typeInfo);
types = listCons((Value *)typeInfo, types);
return((Value *)types);
}


Value *counts() {
List *cnts = empty_list;
cnts = listCons(numberValue(1083), cnts);
return((Value *)cnts);
}

