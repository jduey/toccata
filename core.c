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


// --------- pr* --------------
Function fn_179;
Value *arityImpl_180(List *closures, Value *arg0) {
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
Function fn_179 = {FunctionType, -1, "pr*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_180}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[17];} _str_33 = {1, -1, 16,":match*-two-args"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[16];} _str_32 = {1, -1, 15,":match*-one-arg"};
ProtoImpls *protoImpls_182;
Function protoFn_183;
Value *protoFnImpl_188(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_182);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'bippity' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_189 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_188};
Function protoFn_183 = {FunctionType, -1, "bippity", 1, {&protoFnArity_189}};

ProtoImpls *protoImpls_185;
Function protoFn_186;
Value *arityImpl_190(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_180(empty_list, (Value *)&_str_32);
return(rslt0);
};

Value *protoFnImpl_192(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_185);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'match*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_193 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_192};
Value *protoFnImpl_194(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_185);
  if(implFn == (Function *)0) {
   fprintf(stderr, "\n*** Could not find proto impl for 'match*' %s\n", extractStr(protoFnImpl_25(empty_list, arg0)));
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
FnArity protoFnArity_195 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_194};
Function defaultFn_187 = {FunctionType, -1, "match*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_190}}};

Function protoFn_186 = {FunctionType, -1, "match*", 2, {&protoFnArity_193,
&protoFnArity_195}};


// --------- alert --------------
Function fn_196;
Value *arityImpl_197(List *closures, Value *arg0, Value *arg1) {
Value *cond0;

if (isTrue(arg0)) {
dec_and_free(arg0);
incRef(var_75);
cond0 = var_75;
} else {
dec_and_free(arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_11(empty_list, var_53, arg1);
} else {
FnArity *arity1 = findFnArity(var_53, 1);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
rslt4 = fn3(arity1->closures, arg1);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(arg1);
varArgs2 = (List *)listCons(arg1, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
return(cond0);
};


// --------- alert main body --------------
Function fn_196 = {FunctionType, -1, "alert", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_197}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[53];} _str_34 = {1, -1, 52,"*** call to 'instance?' with unknown type parameter."};
ProtoImpls *protoImpls_199;
Function protoFn_200;
Value *arityImpl_202(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_99(empty_list, arg0);
Value *rslt4 = arityImpl_112(empty_list, (Value *)&_num_2, rslt3);
dec_and_free(rslt3);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
Value *rslt5 = arityImpl_99(empty_list, arg1);
Value *rslt6 = arityImpl_112(empty_list, arg0, rslt5);
incRef(rslt6);
cond0 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
} else {
dec_and_free(rslt4);
Value *rslt1 = arityImpl_180(empty_list, (Value *)&_str_34);
Value *rslt2 = arityImpl_96(empty_list);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
return(cond0);
};

Value *protoFnImpl_203(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_199);
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
FnArity protoFnArity_204 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_203};
Function defaultFn_201 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_202}}};

Function protoFn_200 = {FunctionType, -1, "instance?", 1, {&protoFnArity_204}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[29];} _str_35 = {1, -1, 28,"'flat-map' not implemented: "};
ProtoImpls *protoImpls_205;
Function protoFn_206;
Value *arityImpl_211(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_25(empty_list, arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_35, rslt0);
} else {
FnArity *arity1 = findFnArity(var_53, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_35, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_35);
varArgs2 = (List *)listCons((Value *)&_str_35, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *protoFnImpl_212(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_205);
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
FnArity protoFnArity_213 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_212};
Function defaultFn_207 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_211}}};

Function protoFn_206 = {FunctionType, -1, "flat-map", 1, {&protoFnArity_213}};

ProtoImpls *protoImpls_208;
Function protoFn_209;

// --------- anon --------------
Function fn_215;
Value *arityImpl_216(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- anon main body --------------
Function fn_215 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_216}}};

Value *arityImpl_214(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_212(empty_list, arg0, (Value *)&fn_215);
return(rslt1);
};

Value *protoFnImpl_217(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_208);
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
FnArity protoFnArity_218 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_217};
Function defaultFn_210 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_214}}};

Function protoFn_209 = {FunctionType, -1, "flatten", 1, {&protoFnArity_218}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[30];} _str_36 = {1, -1, 29,"'duplicate' not implemented: "};
ProtoImpls *protoImpls_219;
Function protoFn_220;
Value *protoFnImpl_228(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_219);
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
FnArity protoFnArity_229 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_228};
Function protoFn_220 = {FunctionType, -1, "extend", 1, {&protoFnArity_229}};

ProtoImpls *protoImpls_222;
Function protoFn_223;
Value *arityImpl_230(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_25(empty_list, arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_36, rslt0);
} else {
FnArity *arity1 = findFnArity(var_53, 2);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
incRef(rslt4);
dec_and_free(rslt0);
dec_and_free(rslt4);
return(rslt4);
};

Value *protoFnImpl_231(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_222);
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
FnArity protoFnArity_232 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_231};
Function defaultFn_224 = {FunctionType, -1, "duplicate", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_230}}};

Function protoFn_223 = {FunctionType, -1, "duplicate", 1, {&protoFnArity_232}};

ProtoImpls *protoImpls_225;
Function protoFn_226;
Value *protoFnImpl_233(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_225);
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
FnArity protoFnArity_234 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_233};
Function protoFn_226 = {FunctionType, -1, "extract", 1, {&protoFnArity_234}};

// forward declaration for 'comprehend'
Value *var_235;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_37 = {1, -1, 26,"*** 'wrap' not implemented"};
ProtoImpls *protoImpls_236;
Function protoFn_237;
Value *arityImpl_242(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_53)->type != FunctionType) {
rslt3 = protoFnImpl_11(empty_list, var_53, (Value *)&_str_37);
} else {
FnArity *arity0 = findFnArity(var_53, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_37);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef((Value *)&_str_37);
varArgs1 = (List *)listCons((Value *)&_str_37, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
return(rslt3);
};

Value *protoFnImpl_243(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_236);
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
FnArity protoFnArity_244 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_243};
Function defaultFn_238 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_242}}};

Function protoFn_237 = {FunctionType, -1, "wrap", 1, {&protoFnArity_244}};

ProtoImpls *protoImpls_239;
Function protoFn_240;

// --------- anon --------------
Function fn_246;
Value *arityImpl_247(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4;
if((var_235)->type != FunctionType) {
rslt4 = protoFnImpl_13(empty_list, var_235, arg0, val0);
} else {
FnArity *arity1 = findFnArity(var_235, 2);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_235)->name);
  abort();
}
}
return(rslt4);
};


// --------- anon --------------
Function fn_248;
Value *arityImpl_249(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
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
Value *rslt5 = protoFnImpl_243(empty_list, val0, rslt4);
incRef(rslt5);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *arityImpl_245(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = FnArityType;
arity_4->count = 1;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_249;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
Function *fn_248 = malloc_function(1);
fn_248->type = FunctionType;
fn_248->name = "anon";
fn_248->arityCount = 1;
fn_248->arities[0] = arity_4;
Value *rslt5 = protoFnImpl_212(empty_list, arg0, (Value *)fn_248);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt5);
dec_and_free((Value *)fn_248);
} else {
dec_and_free(rslt3);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = FnArityType;
arity_1->count = 1;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_247;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_246 = malloc_function(1);
fn_246->type = FunctionType;
fn_246->name = "anon";
fn_246->arityCount = 1;
fn_246->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_212(empty_list, arg0, (Value *)fn_246);
incRef(rslt2);
cond0 = rslt2;
dec_and_free((Value *)fn_246);
dec_and_free(rslt2);
}
return(cond0);
};

Value *protoFnImpl_250(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_239);
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
FnArity protoFnArity_251 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_250};
Function defaultFn_241 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_245}}};

Function protoFn_240 = {FunctionType, -1, "apply*", 1, {&protoFnArity_251}};


// --------- list --------------
Function fn_252;
Value *arityImpl_253(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_252 = {FunctionType, -1, "list", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_253}}};

ProtoImpls *protoImpls_255;
Function protoFn_256;

// --------- anon --------------
Function fn_259;
Value *arityImpl_260(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
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
Value *rslt6 = protoFnImpl_243(empty_list, val0, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};

Value *arityImpl_258(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = FnArityType;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_260;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_259 = malloc_function(1);
fn_259->type = FunctionType;
fn_259->name = "anon";
fn_259->arityCount = 1;
fn_259->arities[0] = arity_0;
Value *rslt1 = protoFnImpl_212(empty_list, arg0, (Value *)fn_259);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free((Value *)fn_259);
return(rslt1);
};

Value *protoFnImpl_261(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_255);
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
FnArity protoFnArity_262 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_261};
Function defaultFn_257 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_258}}};

Function protoFn_256 = {FunctionType, -1, "map", 1, {&protoFnArity_262}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_38 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_263;
Function protoFn_264;
Value *arityImpl_266(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_25(empty_list, arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_38, rslt0);
} else {
FnArity *arity1 = findFnArity(var_53, 2);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *protoFnImpl_267(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_263);
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
FnArity protoFnArity_268 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_267};
Function defaultFn_265 = {FunctionType, -1, "name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_266}}};

Function protoFn_264 = {FunctionType, -1, "name", 1, {&protoFnArity_268}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_39 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_269;
Function protoFn_270;
Value *arityImpl_272(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_25(empty_list, arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_39, rslt0);
} else {
FnArity *arity1 = findFnArity(var_53, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_39, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_39);
varArgs2 = (List *)listCons((Value *)&_str_39, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *protoFnImpl_273(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_269);
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
FnArity protoFnArity_274 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_273};
Function defaultFn_271 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_272}}};

Function protoFn_270 = {FunctionType, -1, "string-list", 1, {&protoFnArity_274}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_40 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_275;
Function protoFn_276;
Value *arityImpl_278(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_25(empty_list, arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_40, rslt0);
} else {
FnArity *arity1 = findFnArity(var_53, 2);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType2 *fn3 = (FnType2 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_40, rslt0);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_40);
varArgs2 = (List *)listCons((Value *)&_str_40, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *protoFnImpl_279(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_275);
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
FnArity protoFnArity_280 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_279};
Function defaultFn_277 = {FunctionType, -1, "serialize", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_278}}};

Function protoFn_276 = {FunctionType, -1, "serialize", 1, {&protoFnArity_280}};

Number _num_13 = {2, -1, 0};
ProtoImpls *protoImpls_281;
Function protoFn_282;
Value *arityImpl_284(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt1 = arityImpl_102(empty_list, arg0, arg1);

if (isTrue(rslt1)) {
dec_and_free(rslt1);
Value *rslt2 = protoFnImpl_27(empty_list, arg0);
Value *rslt3 = protoFnImpl_27(empty_list, arg1);
Value *rslt7;
FnArity *arity4 = findFnArity((Value *)&protoFn_282, 2);
if(arity4 != (FnArity *)0 && !arity4->variadic) {
FnType2 *fn6 = (FnType2 *)arity4->fn;
rslt7 = fn6(arity4->closures, rslt2, rslt3);
} else if(arity4 != (FnArity *)0 && arity4->variadic) {
FnType1 *fn6 = (FnType1 *)arity4->fn;
List *varArgs5 = empty_list;
incRef(rslt3);
varArgs5 = (List *)listCons(rslt3, varArgs5);
incRef(rslt2);
varArgs5 = (List *)listCons(rslt2, varArgs5);
rslt7 = fn6(arity4->closures, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&protoFn_282)->name);
  abort();
}
incRef(rslt7);
cond0 = rslt7;
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
} else {
dec_and_free(rslt1);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
}
return(cond0);
};

Value *protoFnImpl_285(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_281);
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
FnArity protoFnArity_286 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_285};
Function defaultFn_283 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_284}}};

Function protoFn_282 = {FunctionType, -1, "=*", 1, {&protoFnArity_286}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_41 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_287;
Function protoFn_288;
Value *arityImpl_290(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_53)->type != FunctionType) {
rslt3 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_41, arg0);
} else {
FnArity *arity0 = findFnArity(var_53, 2);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType2 *fn2 = (FnType2 *)arity0->fn;
rslt3 = fn2(arity0->closures, (Value *)&_str_41, arg0);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
incRef((Value *)&_str_41);
varArgs1 = (List *)listCons((Value *)&_str_41, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt4 = arityImpl_96(empty_list);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};

Value *protoFnImpl_291(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_287);
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
FnArity protoFnArity_292 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_291};
Function defaultFn_289 = {FunctionType, -1, "<*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_290}}};

Function protoFn_288 = {FunctionType, -1, "<*", 1, {&protoFnArity_292}};

ProtoImpls *protoImpls_293;
Function protoFn_294;
Value *protoFnImpl_311(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_293);
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
FnArity protoFnArity_312 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_311};
Function protoFn_294 = {FunctionType, -1, "empty", 1, {&protoFnArity_312}};

ProtoImpls *protoImpls_296;
Function protoFn_297;
Value *protoFnImpl_313(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_296);
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
FnArity protoFnArity_314 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_313};
Function protoFn_297 = {FunctionType, -1, "count", 1, {&protoFnArity_314}};

ProtoImpls *protoImpls_299;
Function protoFn_300;
Value *protoFnImpl_315(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_299);
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
FnArity protoFnArity_316 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_315};
Function protoFn_300 = {FunctionType, -1, "conj", 1, {&protoFnArity_316}};

ProtoImpls *protoImpls_302;
Function protoFn_303;
Value *protoFnImpl_317(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_302);
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
FnArity protoFnArity_318 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_317};
Function protoFn_303 = {FunctionType, -1, "destruct", 1, {&protoFnArity_318}};

ProtoImpls *protoImpls_305;
Function protoFn_306;
Value *protoFnImpl_319(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_305);
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
FnArity protoFnArity_320 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_319};
Function protoFn_306 = {FunctionType, -1, "empty?", 1, {&protoFnArity_320}};

ProtoImpls *protoImpls_308;
Function protoFn_309;
Value *protoFnImpl_321(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_308);
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
FnArity protoFnArity_322 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_321};
Function protoFn_309 = {FunctionType, -1, "reduce", 1, {&protoFnArity_322}};


// --------- not-empty? --------------
Function fn_323;
Value *arityImpl_324(List *closures, Value *arg0) {
Value *cond0;
Value *rslt1 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt1)) {
dec_and_free(rslt1);
incRef(var_76);
cond0 = var_76;
} else {
dec_and_free(rslt1);
incRef(var_75);
cond0 = var_75;
}
return(cond0);
};


// --------- not-empty? main body --------------
Function fn_323 = {FunctionType, -1, "not-empty?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_324}}};

ProtoImpls *protoImpls_326;
Function protoFn_327;
Value *protoFnImpl_341(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_326);
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
FnArity protoFnArity_342 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_341};
Function protoFn_327 = {FunctionType, -1, "rest", 1, {&protoFnArity_342}};

ProtoImpls *protoImpls_329;
Function protoFn_330;
Value *protoFnImpl_343(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_329);
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
FnArity protoFnArity_344 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_343};
Function protoFn_330 = {FunctionType, -1, "seq", 1, {&protoFnArity_344}};

ProtoImpls *protoImpls_332;
Function protoFn_333;
Value *protoFnImpl_345(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_332);
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
FnArity protoFnArity_346 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_345};
Function protoFn_333 = {FunctionType, -1, "first", 1, {&protoFnArity_346}};

ProtoImpls *protoImpls_335;
Function protoFn_336;
Value *protoFnImpl_347(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_335);
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
FnArity protoFnArity_348 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_347};
Function protoFn_336 = {FunctionType, -1, "m-first", 1, {&protoFnArity_348}};

ProtoImpls *protoImpls_338;
Function protoFn_339;
Value *arityImpl_349(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};

Value *protoFnImpl_350(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_338);
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
FnArity protoFnArity_351 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_350};
Function defaultFn_340 = {FunctionType, -1, "seq?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_349}}};

Function protoFn_339 = {FunctionType, -1, "seq?", 1, {&protoFnArity_351}};


// --------- second --------------
Function fn_352;
Value *arityImpl_353(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_341(empty_list, arg0);
Value *rslt1 = protoFnImpl_345(empty_list, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- second main body --------------
Function fn_352 = {FunctionType, -1, "second", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_353}}};

ProtoImpls *protoImpls_355;
Function protoFn_356;
Value *protoFnImpl_358(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_355);
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
FnArity protoFnArity_359 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_358};
Function protoFn_356 = {FunctionType, -1, "traverse", 1, {&protoFnArity_359}};

ProtoImpls *protoImpls_360;
Function protoFn_361;
Value *protoFnImpl_363(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_360);
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
FnArity protoFnArity_364 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_363};
Function protoFn_361 = {FunctionType, -1, "crush", 1, {&protoFnArity_364}};

ProtoImpls *protoImpls_365;
Function protoFn_366;
Value *protoFnImpl_371(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_365);
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
FnArity protoFnArity_372 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_371};
Function protoFn_366 = {FunctionType, -1, "comp*", 1, {&protoFnArity_372}};

ProtoImpls *protoImpls_368;
Function protoFn_369;
Value *protoFnImpl_373(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_368);
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
FnArity protoFnArity_374 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_373};
Function protoFn_369 = {FunctionType, -1, "zero", 1, {&protoFnArity_374}};


// --------- apply --------------
Function fn_375;
Value *arityImpl_376(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt0 = protoFnImpl_250(empty_list, arg0, arg1);
return(rslt0);
};

// --------- apply main body --------------
Function fn_375 = {FunctionType, -1, "apply", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_376}}};


// --------- apply-to --------------
Function fn_378;
Value *arityImpl_379(List *closures, Value *arg0) {
Value *rslt3;
if((arg0)->type != FunctionType) {
rslt3 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity0 = findFnArity(arg0, 0);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType0 *fn2 = (FnType0 *)arity0->fn;
rslt3 = fn2(arity0->closures);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
return(rslt3);
};

Value *arityImpl_380(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt0 = arityImpl_141(empty_list, arg1);
Value *rslt1 = protoFnImpl_243(empty_list, rslt0, arg0);
Value *rslt2 = protoFnImpl_250(empty_list, rslt1, arg1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};

// --------- apply-to main body --------------
Function fn_378 = {FunctionType, -1, "apply-to", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_379}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_380}}};


// --------- comp --------------
Function fn_382;
Value *arityImpl_383(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond0;
Value *rslt2 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt2);
Value *rslt1 = protoFnImpl_371(empty_list, arg0, arg1);
incRef(rslt1);
cond0 = rslt1;
dec_and_free(rslt1);
}
return(cond0);
};

// --------- comp main body --------------
Function fn_382 = {FunctionType, -1, "comp", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_383}}};

ProtoImpls *protoImpls_385;
Function protoFn_386;
Value *protoFnImpl_394(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_385);
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
FnArity protoFnArity_395 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_394};
Function protoFn_386 = {FunctionType, -1, "get*", 1, {&protoFnArity_395}};

ProtoImpls *protoImpls_388;
Function protoFn_389;
Value *protoFnImpl_396(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_388);
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
FnArity protoFnArity_397 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_396};
Function protoFn_389 = {FunctionType, -1, "assoc*", 1, {&protoFnArity_397}};

ProtoImpls *protoImpls_391;
Function protoFn_392;
Value *protoFnImpl_398(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_391);
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
FnArity protoFnArity_399 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_398};
Function protoFn_392 = {FunctionType, -1, "hash-seq", 1, {&protoFnArity_399}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[26];} _str_42 = {1, -1, 25,"'get' not implemented for"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_43 = {1, -1, 2,": "};
SubString _kw_1 = {5, -1, 2, 0, 0, ":k"};
SubString _kw_0 = {5, -1, 2, 0, 0, ":m"};
ProtoImpls *protoImpls_400;
Function protoFn_401;
Value *protoFnImpl_415(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_400);
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
FnArity protoFnArity_416 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_415};
Function protoFn_401 = {FunctionType, -1, "assoc", 1, {&protoFnArity_416}};

ProtoImpls *protoImpls_403;
Function protoFn_404;
Value *protoFnImpl_417(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_403);
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
FnArity protoFnArity_418 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_417};
Function protoFn_404 = {FunctionType, -1, "dissoc", 1, {&protoFnArity_418}};

ProtoImpls *protoImpls_406;
Function protoFn_407;
Value *protoFnImpl_419(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_406);
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
FnArity protoFnArity_420 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_419};
Function protoFn_407 = {FunctionType, -1, "vals", 1, {&protoFnArity_420}};

ProtoImpls *protoImpls_409;
Function protoFn_410;
Value *arityImpl_421(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_25(empty_list, arg0);
Value *rslt4;
if((var_53)->type != FunctionType) {
rslt4 = protoFnImpl_23(empty_list, var_53, (Value *)&_str_42, rslt0, (Value *)&_str_43, (Value *)&_kw_0, arg0, (Value *)&_kw_1, arg1);
} else {
FnArity *arity1 = findFnArity(var_53, 7);
if(arity1 != (FnArity *)0 && !arity1->variadic) {
FnType7 *fn3 = (FnType7 *)arity1->fn;
rslt4 = fn3(arity1->closures, (Value *)&_str_42, rslt0, (Value *)&_str_43, (Value *)&_kw_0, arg0, (Value *)&_kw_1, arg1);
} else if(arity1 != (FnArity *)0 && arity1->variadic) {
FnType1 *fn3 = (FnType1 *)arity1->fn;
List *varArgs2 = empty_list;
incRef(arg1);
varArgs2 = (List *)listCons(arg1, varArgs2);
incRef((Value *)&_kw_1);
varArgs2 = (List *)listCons((Value *)&_kw_1, varArgs2);
incRef(arg0);
varArgs2 = (List *)listCons(arg0, varArgs2);
incRef((Value *)&_kw_0);
varArgs2 = (List *)listCons((Value *)&_kw_0, varArgs2);
incRef((Value *)&_str_43);
varArgs2 = (List *)listCons((Value *)&_str_43, varArgs2);
incRef(rslt0);
varArgs2 = (List *)listCons(rslt0, varArgs2);
incRef((Value *)&_str_42);
varArgs2 = (List *)listCons((Value *)&_str_42, varArgs2);
rslt4 = fn3(arity1->closures, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *protoFnImpl_422(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_409);
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
FnArity protoFnArity_423 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_422};
Function defaultFn_411 = {FunctionType, -1, "get", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_421}}};

Function protoFn_410 = {FunctionType, -1, "get", 1, {&protoFnArity_423}};

ProtoImpls *protoImpls_412;
Function protoFn_413;
Value *protoFnImpl_424(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_412);
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
FnArity protoFnArity_425 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_424};
Function protoFn_413 = {FunctionType, -1, "keys", 1, {&protoFnArity_425}};

ProtoImpls *protoImpls_426;
Function protoFn_427;
Value *protoFnImpl_429(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_426);
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
FnArity protoFnArity_430 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_429};
Function protoFn_427 = {FunctionType, -1, "sha1", 1, {&protoFnArity_430}};


// --------- not --------------
Function fn_431;
Value *arityImpl_432(List *closures, Value *arg0) {
Value *cond0;

if (isTrue(arg0)) {
dec_and_free(arg0);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(arg0);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
}
return(cond0);
};


// --------- not main body --------------
Function fn_431 = {FunctionType, -1, "not", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_432}}};


// --------- and --------------
Function fn_434;
Value *arityImpl_435(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *cond0;
Value *rslt1 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt1)) {
dec_and_free(rslt1);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt1);
Value *rslt2 = arityImpl_141(empty_list, arg0);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
Value *rslt3 = arityImpl_144(empty_list, arg0);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
Value *rslt6 = protoFnImpl_250(empty_list, (Value *)&fn_434, rslt5);
incRef(rslt6);
cond0 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt3);
} else {
dec_and_free(rslt2);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
}
}
return(cond0);
};

// --------- and main body --------------
Function fn_434 = {FunctionType, -1, "and", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_435}}};


// --------- or --------------
Function fn_437;
Value *arityImpl_438(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *cond0;
Value *rslt5 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt5);
Value *rslt6 = arityImpl_141(empty_list, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt6);
Value *rslt1 = arityImpl_144(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_253(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = protoFnImpl_250(empty_list, (Value *)&fn_437, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
}
return(cond0);
};

// --------- or main body --------------
Function fn_437 = {FunctionType, -1, "or", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_438}}};


// --------- = --------------
Function fn_440;
Value *arityImpl_441(List *closures, Value *arg0) {
incRef((Value *)&_num_1);
return((Value *)&_num_1);
};

Value *arityImpl_442(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_285(empty_list, arg0, arg1);
return(rslt0);
};

Value *arityImpl_443(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond0;
Value *rslt1 = arityImpl_141(empty_list, arg1);
Value *rslt2 = protoFnImpl_285(empty_list, arg0, rslt1);
dec_and_free(rslt1);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_253(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_250(empty_list, (Value *)&fn_440, rslt4);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
} else {
dec_and_free(rslt2);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
}
return(cond0);
};

// --------- = main body --------------
Function fn_440 = {FunctionType, -1, "=", 3, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_441}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_442}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_443}}};


// --------- partial --------------
Function fn_445;

// --------- anon --------------
Function fn_447;
Value *arityImpl_448(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_253(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = protoFnImpl_371(empty_list, val1, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
Value *rslt6 = arityImpl_253(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_250(empty_list, val0, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};
Value *arityImpl_446(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
FnArity *arity_0 = malloc_fnArity();
arity_0->type = FnArityType;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_448;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
Function *fn_447 = malloc_function(1);
fn_447->type = FunctionType;
fn_447->name = "anon";
fn_447->arityCount = 1;
fn_447->arities[0] = arity_0;
return((Value *)fn_447);
};

// --------- partial main body --------------
Function fn_445 = {FunctionType, -1, "partial", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_446}}};

// forward declaration for 'maybe-val'
Value *var_450;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_44 = {1, -1, 9,"<nothing>"};

// --------- flatten_impl --------------
Function fn_452;
Value *arityImpl_469(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- flatten_impl main body --------------
Function fn_452 = {FunctionType, -1, "flatten_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_469}}};

Value *protoImpl_470(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_451 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_470}}};


// --------- flat-map_impl --------------
Function fn_454;
Value *arityImpl_471(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- flat-map_impl main body --------------
Function fn_454 = {FunctionType, -1, "flat-map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_471}}};

Value *protoImpl_472(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_453 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_472}}};


// --------- wrap_impl --------------
Function fn_456;
Value *arityImpl_473(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((var_450)->type != FunctionType) {
rslt3 = protoFnImpl_11(empty_list, var_450, arg1);
} else {
FnArity *arity0 = findFnArity(var_450, 1);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg1);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_450)->name);
  abort();
}
}
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_456 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_473}}};

Value *protoImpl_474(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_455 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_474}}};


// --------- apply*_impl --------------
Function fn_458;
Value *arityImpl_475(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- apply*_impl main body --------------
Function fn_458 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_475}}};

Value *protoImpl_476(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_457 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_476}}};


// --------- zero_impl --------------
Function fn_460;
Value *arityImpl_477(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- zero_impl main body --------------
Function fn_460 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_477}}};

Value *protoImpl_478(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_459 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_478}}};


// --------- comp*_impl --------------
Function fn_462;
Value *arityImpl_479(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt4);
Value *rslt1 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = protoFnImpl_341(empty_list, arg1);
Value *rslt3 = protoFnImpl_371(empty_list, rslt1, rslt2);
incRef(rslt3);
cond0 = rslt3;
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_462 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_479}}};

Value *protoImpl_480(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_461 = {FunctionType, -1, "comp*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_480}}};


// --------- =*_impl --------------
Function fn_464;
Value *arityImpl_481(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_102(empty_list, arg0, arg1);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_464 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_481}}};

Value *protoImpl_482(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_463 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_482}}};


// --------- string-list_impl --------------
Function fn_466;
Value *arityImpl_483(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_44);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_44, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_466 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_483}}};

Value *protoImpl_484(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_465 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_484}}};


// --------- map_impl --------------
Function fn_468;
Value *arityImpl_485(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- map_impl main body --------------
Function fn_468 = {FunctionType, -1, "map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_485}}};

Value *protoImpl_486(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_467 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_486}}};

ReifiedVal reified_487 = {13, -1, 9, {(Value *)&fn_452, (Value *)&fn_454, (Value *)&fn_456, (Value *)&fn_458, (Value *)&fn_460, (Value *)&fn_462, (Value *)&fn_464, (Value *)&fn_466, (Value *)&fn_468}};

// --------- any? --------------
Function fn_489;
Value *arityImpl_490(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_319(empty_list, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt3);
Value *rslt4 = protoFnImpl_345(empty_list, arg1);
Value *rslt8;
if((arg0)->type != FunctionType) {
rslt8 = protoFnImpl_11(empty_list, arg0, rslt4);
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
dec_and_free((Value *)varArgs6);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
dec_and_free(rslt4);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt8);
Value *rslt1 = protoFnImpl_341(empty_list, arg1);
Value *rslt2 = arityImpl_490(closures, arg0, rslt1);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- any? main body --------------
Function fn_489 = {FunctionType, -1, "any?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_490}}};

ProtoImpls *protoImpls_492;
Function protoFn_493;
Value *protoFnImpl_495(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_492);
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
FnArity protoFnArity_496 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_495};
Function protoFn_493 = {FunctionType, -1, ".v", 1, {&protoFnArity_496}};

Value *protoFnImpl_498(List *, Value *, Value *);
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
Function fn_500;
Value *arityImpl_505(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&protoFn_1);
varArgs0 = (List *)listCons((Value *)(Value *)&protoFn_1, varArgs0);
Value *rslt1 = arityImpl_376(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
return(rslt1);
};


// --------- apply*_impl main body --------------
Function fn_500 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_505}}};

Value *protoImpl_506(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_499 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_506}}};


// --------- invoke_impl --------------
Function fn_502;

// --------- flatten_impl --------------
Function fn_509;
Value *arityImpl_530(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_531(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_508 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_531}}};


// --------- flat-map_impl --------------
Function fn_511;
Value *arityImpl_532(List *closures, Value *arg0, Value *arg1) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4;
if((arg1)->type != FunctionType) {
rslt4 = protoFnImpl_11(empty_list, arg1, val0);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
return(rslt4);
};

Value *protoImpl_533(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_510 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_533}}};


// --------- wrap_impl --------------
Function fn_513;
Value *arityImpl_534(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_498(empty_list, var_450, arg1);
return(rslt0);
};


// --------- wrap_impl main body --------------
Function fn_513 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_534}}};

Value *protoImpl_535(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_512 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_535}}};


// --------- apply*_impl --------------
Function fn_515;
Value *arityImpl_536(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
List *varArgs7 = empty_list;
incRef((Value *)(Value *)&reified_487);
varArgs7 = (List *)listCons((Value *)(Value *)&reified_487, varArgs7);
incRef((Value *)(Value *)&fn_440);
varArgs7 = (List *)listCons((Value *)(Value *)&fn_440, varArgs7);
Value *rslt8 = arityImpl_446(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = arityImpl_490(empty_list, arg1, rslt8);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
} else {
dec_and_free(rslt9);
Value *rslt1 = protoFnImpl_495(empty_list, arg0);
Value *rslt2 = protoFnImpl_261(empty_list, arg1, (Value *)&protoFn_493);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
Value *rslt4 = arityImpl_253(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_250(empty_list, rslt1, rslt4);
Value *rslt6 = protoFnImpl_498(empty_list, var_450, rslt5);
incRef(rslt6);
cond0 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- apply*_impl main body --------------
Function fn_515 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_536}}};

Value *protoImpl_537(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_514 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_537}}};


// --------- zero_impl --------------
Function fn_517;
Value *arityImpl_538(List *closures, Value *arg0) {
incRef((Value *)&reified_487);
return((Value *)&reified_487);
};


// --------- zero_impl main body --------------
Function fn_517 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_538}}};

Value *protoImpl_539(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_516 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_539}}};


// --------- comp*_impl --------------
Function fn_519;
Value *arityImpl_540(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- comp*_impl main body --------------
Function fn_519 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_540}}};

Value *protoImpl_541(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_518 = {FunctionType, -1, "comp*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_541}}};


// --------- string-list_impl --------------
Function fn_521;
Value *arityImpl_542(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_45);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_45, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_495(empty_list, arg0);
Value *rslt3 = protoFnImpl_273(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_46, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
Value *rslt7 = arityImpl_253(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = protoFnImpl_371(empty_list, rslt1, rslt7);
incRef(rslt8);
dec_and_free(rslt1);
dec_and_free(rslt8);
dec_and_free(rslt5);
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt8);
};


// --------- string-list_impl main body --------------
Function fn_521 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_542}}};

Value *protoImpl_543(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_520 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_543}}};


// --------- map_impl --------------
Function fn_523;
Value *arityImpl_544(List *closures, Value *arg0, Value *arg1) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4;
if((arg1)->type != FunctionType) {
rslt4 = protoFnImpl_11(empty_list, arg1, val0);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
Value *rslt5 = protoFnImpl_498(empty_list, var_450, rslt4);
incRef(rslt5);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *protoImpl_545(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_522 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_545}}};


// --------- type-args_impl --------------
Function fn_525;
Value *arityImpl_546(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs1 = empty_list;
incRef((Value *)val0);
varArgs1 = (List *)listCons((Value *)val0, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};

Value *protoImpl_547(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_524 = {FunctionType, -1, "type-args", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_547}}};


// --------- type-name_impl --------------
Function fn_527;
Value *arityImpl_548(List *closures, Value *arg0) {
incRef((Value *)&_str_47);
return((Value *)&_str_47);
};


// --------- type-name_impl main body --------------
Function fn_527 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_548}}};

Value *protoImpl_549(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_526 = {FunctionType, -1, "type-name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_549}}};


// --------- .v_impl --------------
Function fn_529;
Value *arityImpl_550(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val0);
return(val0);
};

Value *protoImpl_551(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_528 = {FunctionType, -1, ".v", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_551}}};

Value *arityImpl_507(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = FnArityType;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_530;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_509 = malloc_function(1);
fn_509->type = FunctionType;
fn_509->name = "flatten_impl";
fn_509->arityCount = 1;
fn_509->arities[0] = arity_0;
FnArity *arity_1 = malloc_fnArity();
arity_1->type = FnArityType;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_532;
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_511 = malloc_function(1);
fn_511->type = FunctionType;
fn_511->name = "flat-map_impl";
fn_511->arityCount = 1;
fn_511->arities[0] = arity_1;
FnArity *arity_7 = malloc_fnArity();
arity_7->type = FnArityType;
arity_7->count = 2;
arity_7->closures = empty_list;
arity_7->variadic = 0;
arity_7->fn = arityImpl_544;
incRef((Value *)arg1);
arity_7->closures = listCons((Value *)arg1, (List *)arity_7->closures);
Function *fn_523 = malloc_function(1);
fn_523->type = FunctionType;
fn_523->name = "map_impl";
fn_523->arityCount = 1;
fn_523->arities[0] = arity_7;
FnArity *arity_8 = malloc_fnArity();
arity_8->type = FnArityType;
arity_8->count = 1;
arity_8->closures = empty_list;
arity_8->variadic = 0;
arity_8->fn = arityImpl_546;
incRef((Value *)arg1);
arity_8->closures = listCons((Value *)arg1, (List *)arity_8->closures);
Function *fn_525 = malloc_function(1);
fn_525->type = FunctionType;
fn_525->name = "type-args_impl";
fn_525->arityCount = 1;
fn_525->arities[0] = arity_8;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = FnArityType;
arity_10->count = 1;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_550;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_529 = malloc_function(1);
fn_529->type = FunctionType;
fn_529->name = ".v_impl";
fn_529->arityCount = 1;
fn_529->arities[0] = arity_10;
Value *reified_11 = (Value *)malloc_reified(11);
((ReifiedVal *)reified_11)->type = 15;
((ReifiedVal *)reified_11)->implCount = 11;
((ReifiedVal *)reified_11)->impls[0] = (Value *)fn_509;
incRef((Value *)fn_509);
((ReifiedVal *)reified_11)->impls[1] = (Value *)fn_511;
incRef((Value *)fn_511);
((ReifiedVal *)reified_11)->impls[2] = (Value *)&fn_513;
incRef((Value *)&fn_513);
((ReifiedVal *)reified_11)->impls[3] = (Value *)&fn_515;
incRef((Value *)&fn_515);
((ReifiedVal *)reified_11)->impls[4] = (Value *)&fn_517;
incRef((Value *)&fn_517);
((ReifiedVal *)reified_11)->impls[5] = (Value *)&fn_519;
incRef((Value *)&fn_519);
((ReifiedVal *)reified_11)->impls[6] = (Value *)&fn_521;
incRef((Value *)&fn_521);
((ReifiedVal *)reified_11)->impls[7] = (Value *)fn_523;
incRef((Value *)fn_523);
((ReifiedVal *)reified_11)->impls[8] = (Value *)fn_525;
incRef((Value *)fn_525);
((ReifiedVal *)reified_11)->impls[9] = (Value *)&fn_527;
incRef((Value *)&fn_527);
((ReifiedVal *)reified_11)->impls[10] = (Value *)fn_529;
incRef((Value *)fn_529);
incRef(reified_11);
dec_and_free(reified_11);
dec_and_free((Value *)fn_525);
dec_and_free((Value *)fn_529);
dec_and_free((Value *)fn_523);
dec_and_free((Value *)fn_511);
dec_and_free((Value *)fn_509);
return(reified_11);
};


// --------- invoke_impl main body --------------
Function fn_502 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_507}}};

Value *protoFnImpl_498(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_501 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoFnImpl_498}}};


// --------- instance?_impl --------------
Function fn_504;
Value *arityImpl_552(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_99(empty_list, arg1);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_14, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- instance?_impl main body --------------
Function fn_504 = {FunctionType, -1, "instance?_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_552}}};

Value *protoImpl_553(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_503 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_553}}};

ReifiedVal reified_554 = {14, -1, 3, {(Value *)&fn_500, (Value *)&fn_502, (Value *)&fn_504}};
Value *var_450 = (Value *)&reified_554;

// --------- zero_impl --------------
Function fn_556;
Value *arityImpl_561(List *closures, Value *arg0) {
incRef((Value *)&reified_487);
return((Value *)&reified_487);
};


// --------- zero_impl main body --------------
Function fn_556 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_561}}};

Value *protoImpl_562(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_555 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_562}}};


// --------- invoke_impl --------------
Function fn_558;
Value *arityImpl_563(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_498(empty_list, var_450, arg1);
return(rslt0);
};


// --------- invoke_impl main body --------------
Function fn_558 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_563}}};

Value *protoImpl_564(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_557 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_564}}};


// --------- instance?_impl --------------
Function fn_560;
Value *arityImpl_565(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoImpl_553(empty_list, var_450, arg1);
return(rslt0);
};


// --------- instance?_impl main body --------------
Function fn_560 = {FunctionType, -1, "instance?_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_565}}};

Value *protoImpl_566(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_559 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_566}}};

ReifiedVal reified_567 = {16, -1, 3, {(Value *)&fn_556, (Value *)&fn_558, (Value *)&fn_560}};

// --------- m= --------------
Function fn_569;
Value *arityImpl_570(List *closures, Value *arg0) {
Value *rslt0 = protoImpl_564(empty_list, (Value *)&reified_567, arg0);
return(rslt0);
};

Value *arityImpl_571(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt1 = protoFnImpl_285(empty_list, arg0, arg1);

if (isTrue(rslt1)) {
dec_and_free(rslt1);
Value *rslt2 = protoImpl_564(empty_list, (Value *)&reified_567, arg0);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt2);
} else {
dec_and_free(rslt1);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
}
return(cond0);
};

Value *arityImpl_572(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond0;
Value *rslt1 = arityImpl_141(empty_list, arg1);
Value *rslt2 = protoFnImpl_285(empty_list, arg0, rslt1);
dec_and_free(rslt1);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_253(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_250(empty_list, (Value *)&fn_569, rslt4);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
} else {
dec_and_free(rslt2);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
}
return(cond0);
};

// --------- m= main body --------------
Function fn_569 = {FunctionType, -1, "m=", 3, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_570}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_571}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_572}}};


// --------- some --------------
Function fn_574;
Value *arityImpl_575(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt3 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
} else {
dec_and_free(rslt3);
Value *rslt4 = protoFnImpl_345(empty_list, arg0);
Value *rslt8;
if((arg1)->type != FunctionType) {
rslt8 = protoFnImpl_11(empty_list, arg1, rslt4);
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
dec_and_free((Value *)varArgs6);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
dec_and_free(rslt4);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
Value *rslt9 = protoFnImpl_345(empty_list, arg0);
Value *rslt10 = protoImpl_564(empty_list, (Value *)&reified_567, rslt9);
incRef(rslt10);
cond0 = rslt10;
dec_and_free(rslt10);
dec_and_free(rslt9);
} else {
dec_and_free(rslt8);
Value *rslt1 = protoFnImpl_341(empty_list, arg0);
Value *rslt2 = arityImpl_575(closures, rslt1, arg1);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- some main body --------------
Function fn_574 = {FunctionType, -1, "some", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_575}}};


// --------- < --------------
Function fn_577;
Value *arityImpl_578(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_291(empty_list, arg0, arg1);
return(rslt0);
};

Value *arityImpl_579(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond0;
Value *rslt4 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt4);
Value *rslt5 = arityImpl_141(empty_list, arg1);
Value *rslt6 = protoFnImpl_291(empty_list, arg0, rslt5);
Value *rslt7 = arityImpl_432(empty_list, rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt7);
Value *rslt8 = arityImpl_135(empty_list, arg1);
Value *rslt9 = arityImpl_112(empty_list, (Value *)&_num_1, rslt8);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt9);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = protoFnImpl_250(empty_list, (Value *)&fn_577, rslt2);
incRef(rslt3);
cond0 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
}
return(cond0);
};

// --------- < main body --------------
Function fn_577 = {FunctionType, -1, "<", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_578}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_579}}};


// --------- list** --------------
Function fn_581;
Value *arityImpl_582(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt5);
Value *rslt1 = arityImpl_141(empty_list, arg1);
Value *rslt2 = arityImpl_144(empty_list, arg1);
Value *rslt3 = arityImpl_582(closures, rslt1, rslt2);
Value *rslt4 = arityImpl_132(empty_list, arg0, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- list** main body --------------
Function fn_581 = {FunctionType, -1, "list**", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_582}}};


// --------- list* --------------
Function fn_584;
Value *arityImpl_585(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt0 = arityImpl_582(empty_list, arg0, arg1);
return(rslt0);
};

// --------- list* main body --------------
Function fn_584 = {FunctionType, -1, "list*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_585}}};


// --------- filter --------------
Function fn_587;
Value *arityImpl_588(List *closures, Value *arg0, Value *arg1) {
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
Function fn_587 = {FunctionType, -1, "filter", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_588}}};


// --------- remove --------------
Function fn_590;

// --------- anon --------------
Function fn_592;
Value *arityImpl_593(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4;
if((val0)->type != FunctionType) {
rslt4 = protoFnImpl_11(empty_list, val0, arg0);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val0)->name);
  abort();
}
}
Value *rslt5 = arityImpl_432(empty_list, rslt4);
incRef(rslt5);
dec_and_free(rslt5);
dec_and_free(rslt4);
return(rslt5);
};

Value *arityImpl_591(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = FnArityType;
arity_0->count = 1;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_593;
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_592 = malloc_function(1);
fn_592->type = FunctionType;
fn_592->name = "anon";
fn_592->arityCount = 1;
fn_592->arities[0] = arity_0;
Value *rslt1 = arityImpl_588(empty_list, arg0, (Value *)fn_592);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free((Value *)fn_592);
return(rslt1);
};


// --------- remove main body --------------
Function fn_590 = {FunctionType, -1, "remove", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_591}}};


// --------- reverse --------------
Function fn_595;
Value *arityImpl_596(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_311(empty_list, arg0);
Value *rslt1 = protoFnImpl_321(empty_list, arg0, rslt0, (Value *)&protoFn_300);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- reverse main body --------------
Function fn_595 = {FunctionType, -1, "reverse", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_596}}};


// --------- identity --------------
Function fn_598;
Value *arityImpl_599(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_598 = {FunctionType, -1, "identity", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_599}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_48 = {1, -1, 5,"<Fn: "};

// --------- apply*_impl --------------
Function fn_601;
Value *arityImpl_605(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *rslt9;
if((arg0)->type != FunctionType) {
rslt9 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity6 = findFnArity(arg0, 0);
if(arity6 != (FnArity *)0 && !arity6->variadic) {
FnType0 *fn8 = (FnType0 *)arity6->fn;
rslt9 = fn8(arity6->closures);
} else if(arity6 != (FnArity *)0 && arity6->variadic) {
FnType1 *fn8 = (FnType1 *)arity6->fn;
List *varArgs7 = empty_list;
rslt9 = fn8(arity6->closures, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
incRef(rslt9);
cond0 = rslt9;
dec_and_free(rslt9);
} else {
dec_and_free(rslt5);
Value *rslt1 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = protoFnImpl_341(empty_list, arg1);
Value *rslt3 = arityImpl_582(empty_list, rslt1, rslt2);
Value *rslt4 = arityImpl_174(empty_list, arg0, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- apply*_impl main body --------------
Function fn_601 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_605}}};


// --------- zero_impl --------------
Function fn_602;
Value *arityImpl_606(List *closures, Value *arg0) {
incRef((Value *)&fn_598);
return((Value *)&fn_598);
};


// --------- zero_impl main body --------------
Function fn_602 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_606}}};


// --------- comp*_impl --------------
Function fn_603;

// --------- anon --------------
Function fn_608;

// --------- anon --------------
Function fn_610;
Value *arityImpl_611(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
if((arg1)->type != FunctionType) {
rslt3 = protoFnImpl_11(empty_list, arg1, arg0);
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
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
return(rslt3);
};


// --------- anon main body --------------
Function fn_610 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_611}}};

Value *arityImpl_609(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_253(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = protoFnImpl_250(empty_list, val1, rslt3);
Value *rslt6 = protoFnImpl_321(empty_list, val0, rslt4, (Value *)&fn_610);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt6);
};
Value *arityImpl_607(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = FnArityType;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 1;
arity_0->fn = arityImpl_609;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_608 = malloc_function(1);
fn_608->type = FunctionType;
fn_608->name = "anon";
fn_608->arityCount = 1;
fn_608->arities[0] = arity_0;
return((Value *)fn_608);
};


// --------- comp*_impl main body --------------
Function fn_603 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_607}}};


// --------- string-list_impl --------------
Function fn_604;
Value *arityImpl_612(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_147(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_46, varArgs1);
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
incRef((Value *)(Value *)&_str_48);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_48, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_604 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_612}}};


// --------- sha1_impl --------------
Function fn_613;
Value *arityImpl_617(List *closures, Value *arg0) {

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
Function fn_613 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_617}}};


// --------- <*_impl --------------
Function fn_614;
Value *arityImpl_618(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_115(empty_list, arg0, arg1);
return(rslt0);
};


// --------- <*_impl main body --------------
Function fn_614 = {FunctionType, -1, "<*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_618}}};


// --------- =*_impl --------------
Function fn_615;
Value *arityImpl_619(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_112(empty_list, arg0, arg1);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_615 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_619}}};


// --------- string-list_impl --------------
Function fn_616;
Value *arityImpl_620(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_109(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_616 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_620}}};


// --------- comprehend --------------
Function fn_622;
Value *arityImpl_623(List *closures, Value *arg0) {
Value *rslt3;
if((arg0)->type != FunctionType) {
rslt3 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity0 = findFnArity(arg0, 0);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType0 *fn2 = (FnType0 *)arity0->fn;
rslt3 = fn2(arity0->closures);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
return(rslt3);
};


// --------- anon --------------
Function fn_625;
Value *arityImpl_627(List *closures, Value *arg0, Value *arg1) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = arityImpl_132(empty_list, arg1, arg0);
Value *rslt3 = arityImpl_596(empty_list, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
Value *rslt6 = protoFnImpl_250(empty_list, val1, rslt5);
Value *rslt7 = protoFnImpl_243(empty_list, val0, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt7);
};


// --------- anon --------------
Function fn_626;

// --------- anon --------------
Function fn_629;
Value *arityImpl_630(List *closures, Value *arg0, Value *arg1) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = arityImpl_132(empty_list, arg1, arg0);
List *varArgs3 = empty_list;
incRef((Value *)rslt2);
varArgs3 = (List *)listCons((Value *)rslt2, varArgs3);
incRef((Value *)val1);
varArgs3 = (List *)listCons((Value *)val1, varArgs3);
Value *rslt4 = arityImpl_446(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_212(empty_list, val0, rslt4);
incRef(rslt5);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt5);
};

Value *arityImpl_628(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_0 = malloc_fnArity();
arity_0->type = FnArityType;
arity_0->count = 2;
arity_0->closures = empty_list;
arity_0->variadic = 0;
arity_0->fn = arityImpl_630;
incRef((Value *)arg0);
arity_0->closures = listCons((Value *)arg0, (List *)arity_0->closures);
incRef((Value *)arg1);
arity_0->closures = listCons((Value *)arg1, (List *)arity_0->closures);
Function *fn_629 = malloc_function(1);
fn_629->type = FunctionType;
fn_629->name = "anon";
fn_629->arityCount = 1;
fn_629->arities[0] = arity_0;
return((Value *)fn_629);
};


// --------- anon main body --------------
Function fn_626 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_628}}};


// --------- anon --------------
Function fn_631;
Value *arityImpl_632(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
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
Value *rslt6 = protoFnImpl_243(empty_list, val0, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};

Value *arityImpl_624(List *closures, Value *arg0, Value *arg3) {
List *arg4 = (List *)arg3;
Value *arg1 = arg4->head;
if (arg4->tail) arg4->tail->len = arg4->len - 1;
arg4 = arg4->tail;
Value *arg2 = (Value *) arg4;
Value *rslt0 = arityImpl_596(empty_list, arg2);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = FnArityType;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_627;
incRef((Value *)arg0);
arity_1->closures = listCons((Value *)arg0, (List *)arity_1->closures);
incRef((Value *)arg1);
arity_1->closures = listCons((Value *)arg1, (List *)arity_1->closures);
Function *fn_625 = malloc_function(1);
fn_625->type = FunctionType;
fn_625->name = "anon";
fn_625->arityCount = 1;
fn_625->arities[0] = arity_1;
Value *rslt3 = protoFnImpl_321(empty_list, rslt0, (Value *)fn_625, (Value *)&fn_626);
Value *cond4;
Value *rslt8 = arityImpl_135(empty_list, arg2);
Value *rslt9 = arityImpl_112(empty_list, (Value *)&_num_1, rslt8);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
FnArity *arity_10 = malloc_fnArity();
arity_10->type = FnArityType;
arity_10->count = 1;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_632;
incRef((Value *)arg0);
arity_10->closures = listCons((Value *)arg0, (List *)arity_10->closures);
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_631 = malloc_function(1);
fn_631->type = FunctionType;
fn_631->name = "anon";
fn_631->arityCount = 1;
fn_631->arities[0] = arity_10;
Value *rslt11 = protoFnImpl_212(empty_list, arg1, (Value *)fn_631);
incRef(rslt11);
cond4 = rslt11;
dec_and_free(rslt11);
dec_and_free((Value *)fn_631);
} else {
dec_and_free(rslt9);
List *varArgs5 = empty_list;
incRef((Value *)var_129);
varArgs5 = (List *)listCons((Value *)var_129, varArgs5);
incRef((Value *)rslt3);
varArgs5 = (List *)listCons((Value *)rslt3, varArgs5);
Value *rslt6 = arityImpl_446(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_212(empty_list, arg1, rslt6);
incRef(rslt7);
cond4 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free((Value *)fn_625);
dec_and_free(rslt0);
dec_and_free(rslt3);
return(cond4);
};


// --------- comprehend main body --------------
Function fn_622 = {FunctionType, -1, "comprehend", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_623}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_624}}};

Value *var_235 = (Value *)&fn_622;

// --------- list-concat --------------
Function fn_633;
Value *arityImpl_634(List *closures, Value *arg0) {
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
Function fn_633 = {FunctionType, -1, "list-concat", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_634}}};


// --------- list=* --------------
Function fn_636;

// --------- anon --------------
Function fn_638;
Value *arityImpl_639(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_141(empty_list, arg0);
return(rslt0);
};


// --------- anon main body --------------
Function fn_638 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_639}}};

Value *arityImpl_637(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt3);
Value *rslt4 = arityImpl_141(empty_list, arg0);
Value *rslt5 = arityImpl_138(empty_list, rslt4);
dec_and_free(rslt4);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt5);
Value *rslt7 = protoFnImpl_261(empty_list, arg0, (Value *)&fn_638);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
Value *rslt9 = arityImpl_253(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = arityImpl_605(empty_list, (Value *)&fn_440, rslt9);
Value *rslt11 = arityImpl_432(empty_list, rslt10);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt7);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt11);
Value *rslt1 = protoFnImpl_261(empty_list, arg0, (Value *)&protoFn_327);
Value *rslt2 = arityImpl_637(closures, rslt1);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
}
}
return(cond0);
};


// --------- list=* main body --------------
Function fn_636 = {FunctionType, -1, "list=*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_637}}};


// --------- traverse_impl --------------
Function fn_641;
Value *arityImpl_659(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_261(empty_list, arg0, arg1);
Value *rslt1 = arityImpl_141(empty_list, rslt0);
Value *rslt2 = protoFnImpl_243(empty_list, rslt1, (Value *)&fn_252);
Value *rslt3 = protoFnImpl_250(empty_list, rslt2, rslt0);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- traverse_impl main body --------------
Function fn_641 = {FunctionType, -1, "traverse_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_659}}};


// --------- empty?_impl --------------
Function fn_642;
Value *arityImpl_660(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_138(empty_list, arg0);
return(rslt0);
};


// --------- empty?_impl main body --------------
Function fn_642 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_660}}};


// --------- empty_impl --------------
Function fn_643;
Value *arityImpl_661(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- empty_impl main body --------------
Function fn_643 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_661}}};


// --------- conj_impl --------------
Function fn_644;
Value *arityImpl_662(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_132(empty_list, arg1, arg0);
return(rslt0);
};


// --------- conj_impl main body --------------
Function fn_644 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_662}}};


// --------- count_impl --------------
Function fn_645;
Value *arityImpl_663(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_135(empty_list, arg0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_645 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_663}}};


// --------- reduce_impl --------------
Function fn_646;
Value *arityImpl_664(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt10 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(arg1);
cond0 = arg1;
} else {
dec_and_free(rslt10);
Value *rslt1 = arityImpl_141(empty_list, arg0);
Value *rslt2 = arityImpl_144(empty_list, arg0);
Value *rslt6;
if((arg2)->type != FunctionType) {
rslt6 = protoFnImpl_13(empty_list, arg2, arg1, rslt1);
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
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg2)->name);
  abort();
}
}
Value *cond7;
Value *rslt9 = arityImpl_138(empty_list, rslt2);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(rslt6);
cond7 = rslt6;
} else {
dec_and_free(rslt9);
Value *rslt8 = protoFnImpl_321(empty_list, rslt2, rslt6, arg2);
incRef(rslt8);
cond7 = rslt8;
dec_and_free(rslt8);
}
incRef(cond7);
cond0 = cond7;
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(cond7);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- reduce_impl main body --------------
Function fn_646 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_664}}};


// --------- crush_impl --------------
Function fn_647;

// --------- anon --------------
Function fn_666;
Value *arityImpl_667(List *closures, Value *arg0, Value *arg1) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4;
if((val0)->type != FunctionType) {
rslt4 = protoFnImpl_11(empty_list, val0, arg1);
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
dec_and_free((Value *)varArgs2);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val0)->name);
  abort();
}
}
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
Value *rslt6 = arityImpl_253(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_371(empty_list, arg0, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt7);
};

Value *arityImpl_665(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_144(empty_list, arg0);
Value *rslt1 = arityImpl_141(empty_list, arg0);
Value *rslt5;
if((arg1)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, arg1, rslt1);
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
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 2;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_667;
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_666 = malloc_function(1);
fn_666->type = FunctionType;
fn_666->name = "anon";
fn_666->arityCount = 1;
fn_666->arities[0] = arity_6;
Value *rslt7 = arityImpl_664(empty_list, rslt0, rslt5, (Value *)fn_666);
incRef(rslt7);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free((Value *)fn_666);
dec_and_free(rslt5);
dec_and_free(rslt7);
return(rslt7);
};


// --------- crush_impl main body --------------
Function fn_647 = {FunctionType, -1, "crush_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_665}}};


// --------- flat-map_impl --------------
Function fn_648;
Value *arityImpl_668(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_261(empty_list, arg0, arg1);
Value *cond1;
Value *rslt5 = arityImpl_138(empty_list, rslt0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(var_129);
cond1 = var_129;
} else {
dec_and_free(rslt5);
Value *rslt2 = arityImpl_141(empty_list, rslt0);
Value *rslt3 = arityImpl_144(empty_list, rslt0);
Value *rslt4 = protoFnImpl_371(empty_list, rslt2, rslt3);
incRef(rslt4);
cond1 = rslt4;
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};


// --------- flat-map_impl main body --------------
Function fn_648 = {FunctionType, -1, "flat-map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_668}}};


// --------- wrap_impl --------------
Function fn_649;
Value *arityImpl_669(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
return(rslt1);
};


// --------- wrap_impl main body --------------
Function fn_649 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_669}}};


// --------- zero_impl --------------
Function fn_650;
Value *arityImpl_670(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- zero_impl main body --------------
Function fn_650 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_670}}};


// --------- comp*_impl --------------
Function fn_651;
Value *arityImpl_671(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt1 = arityImpl_634(empty_list, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_651 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_671}}};


// --------- =*_impl --------------
Function fn_652;
Value *arityImpl_672(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_99(empty_list, arg0);
Value *rslt5 = arityImpl_99(empty_list, arg1);
Value *rslt6 = arityImpl_112(empty_list, rslt4, rslt5);
Value *rslt7 = arityImpl_432(empty_list, rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt7);
Value *rslt8 = protoFnImpl_313(empty_list, arg0);
Value *rslt9 = protoFnImpl_313(empty_list, arg1);
Value *rslt10 = arityImpl_112(empty_list, rslt8, rslt9);
Value *rslt11 = arityImpl_432(empty_list, rslt10);
dec_and_free(rslt8);
dec_and_free(rslt10);
dec_and_free(rslt9);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt11);
List *varArgs1 = empty_list;
incRef((Value *)arg1);
varArgs1 = (List *)listCons((Value *)arg1, varArgs1);
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_637(empty_list, rslt2);
incRef(rslt3);
cond0 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- =*_impl main body --------------
Function fn_652 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_672}}};


// --------- seq?_impl --------------
Function fn_653;
Value *arityImpl_673(List *closures, Value *arg0) {
incRef(var_75);
return(var_75);
};


// --------- seq?_impl main body --------------
Function fn_653 = {FunctionType, -1, "seq?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_673}}};


// --------- seq_impl --------------
Function fn_654;
Value *arityImpl_674(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_654 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_674}}};


// --------- m-first_impl --------------
Function fn_655;
Value *arityImpl_675(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
} else {
dec_and_free(rslt3);
Value *rslt1 = arityImpl_141(empty_list, arg0);
Value *rslt2 = protoImpl_564(empty_list, (Value *)&reified_567, rslt1);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- m-first_impl main body --------------
Function fn_655 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_675}}};


// --------- first_impl --------------
Function fn_656;
Value *arityImpl_676(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_141(empty_list, arg0);
return(rslt0);
};


// --------- first_impl main body --------------
Function fn_656 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_676}}};


// --------- rest_impl --------------
Function fn_657;
Value *arityImpl_677(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_144(empty_list, arg0);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_657 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_677}}};


// --------- map_impl --------------
Function fn_658;
Value *arityImpl_678(List *closures, Value *arg0, Value *arg1) {
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
Function fn_658 = {FunctionType, -1, "map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_678}}};


// --------- interpose --------------
Function fn_679;

// --------- anon --------------
Function fn_681;
Value *arityImpl_682(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)val0);
varArgs1 = (List *)listCons((Value *)val0, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};

Value *arityImpl_680(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt6);
Value *rslt1 = arityImpl_141(empty_list, arg0);
Value *rslt2 = arityImpl_144(empty_list, arg0);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_682;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_681 = malloc_function(1);
fn_681->type = FunctionType;
fn_681->name = "anon";
fn_681->arityCount = 1;
fn_681->arities[0] = arity_3;
Value *rslt4 = arityImpl_668(empty_list, rslt2, (Value *)fn_681);
Value *rslt5 = arityImpl_132(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt1);
dec_and_free((Value *)fn_681);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- interpose main body --------------
Function fn_679 = {FunctionType, -1, "interpose", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_680}}};

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
Function fn_684;
Value *arityImpl_685(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)(Value *)&_str_49);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_49, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = arityImpl_680(empty_list, arg0, (Value *)&_str_50);
Value *rslt3 = protoFnImpl_212(empty_list, rslt2, (Value *)&protoFn_270);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_51);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_51, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
incRef((Value *)rslt3);
varArgs6 = (List *)listCons((Value *)rslt3, varArgs6);
incRef((Value *)rslt1);
varArgs6 = (List *)listCons((Value *)rslt1, varArgs6);
Value *rslt7 = arityImpl_253(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = arityImpl_634(empty_list, rslt7);
incRef(rslt8);
dec_and_free(rslt1);
dec_and_free(rslt8);
dec_and_free(rslt5);
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt8);
};


// --------- string-list_impl main body --------------
Function fn_684 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_685}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_52 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_53 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_686;
Value *arityImpl_687(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt0 = protoFnImpl_212(empty_list, arg0, (Value *)&protoFn_276);
Value *rslt1 = arityImpl_680(empty_list, rslt0, (Value *)&_str_52);
Value *rslt2 = protoFnImpl_261(empty_list, rslt1, (Value *)&fn_179);
Value *rslt3 = arityImpl_180(empty_list, (Value *)&_str_53);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};

// --------- prn main body --------------
Function fn_686 = {FunctionType, -1, "prn", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_687}}};


// --------- print --------------
Function fn_689;
Value *arityImpl_690(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt0 = arityImpl_680(empty_list, arg0, (Value *)&_str_52);
Value *rslt1 = protoFnImpl_212(empty_list, rslt0, (Value *)&protoFn_270);
Value *rslt2 = protoFnImpl_261(empty_list, rslt1, (Value *)&fn_179);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};

// --------- print main body --------------
Function fn_689 = {FunctionType, -1, "print", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_690}}};


// --------- println --------------
Function fn_692;
Value *arityImpl_693(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt0 = arityImpl_680(empty_list, arg0, (Value *)&_str_52);
Value *rslt1 = protoFnImpl_212(empty_list, rslt0, (Value *)&protoFn_270);
Value *rslt2 = protoFnImpl_261(empty_list, rslt1, (Value *)&fn_179);
Value *rslt3 = arityImpl_180(empty_list, (Value *)&_str_53);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};

// --------- println main body --------------
Function fn_692 = {FunctionType, -1, "println", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_693}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_54 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_696;
Value *arityImpl_697(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt0 = arityImpl_168(empty_list, (Value *)&_str_54);
Value *rslt1 = arityImpl_680(empty_list, arg0, (Value *)&_str_52);
Value *rslt2 = protoFnImpl_212(empty_list, rslt1, (Value *)&protoFn_270);
Value *rslt3 = protoFnImpl_261(empty_list, rslt2, (Value *)&fn_167);
Value *rslt4 = arityImpl_168(empty_list, (Value *)&_str_53);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- print-err main body --------------
Function fn_696 = {FunctionType, -1, "print-err", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_697}}};

Value *var_53 = (Value *)&fn_696;

// --------- inc --------------
Function fn_698;
Value *arityImpl_699(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_118(empty_list, arg0, (Value *)&_num_1);
return(rslt0);
};


// --------- inc main body --------------
Function fn_698 = {FunctionType, -1, "inc", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_699}}};


// --------- + --------------
Function fn_701;
Value *arityImpl_702(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *cond0;
Value *rslt2 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
incRef((Value *)&_num_13);
cond0 = (Value *)&_num_13;
} else {
dec_and_free(rslt2);
Value *rslt1 = protoFnImpl_321(empty_list, arg0, (Value *)&_num_13, (Value *)&fn_117);
incRef(rslt1);
cond0 = rslt1;
dec_and_free(rslt1);
}
return(cond0);
};

// --------- + main body --------------
Function fn_701 = {FunctionType, -1, "+", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_702}}};


// --------- * --------------
Function fn_704;
Value *arityImpl_705(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *cond0;
Value *rslt2 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
incRef((Value *)&_num_1);
cond0 = (Value *)&_num_1;
} else {
dec_and_free(rslt2);
Value *rslt1 = protoFnImpl_321(empty_list, arg0, (Value *)&_num_1, (Value *)&fn_123);
incRef(rslt1);
cond0 = rslt1;
dec_and_free(rslt1);
}
return(cond0);
};

// --------- * main body --------------
Function fn_704 = {FunctionType, -1, "*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_705}}};


// --------- dec --------------
Function fn_707;
Value *arityImpl_708(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_121(empty_list, arg0, (Value *)&_num_1);
return(rslt0);
};


// --------- dec main body --------------
Function fn_707 = {FunctionType, -1, "dec", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_708}}};


// --------- - --------------
Function fn_710;
Value *arityImpl_711(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_712(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond0;
Value *rslt2 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt2);
Value *rslt1 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_120);
incRef(rslt1);
cond0 = rslt1;
dec_and_free(rslt1);
}
return(cond0);
};

// --------- - main body --------------
Function fn_710 = {FunctionType, -1, "-", 2, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_711}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_712}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_55 = {1, -1, 0,""};

// --------- sha1_impl --------------
Function fn_714;
Value *arityImpl_726(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
String *strVal = (String *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)strVal->buffer, strVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_714 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_726}}};


// --------- empty?_impl --------------
Function fn_715;
Value *arityImpl_727(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_153(empty_list, arg0);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_13, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_715 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_727}}};


// --------- empty_impl --------------
Function fn_716;
Value *arityImpl_728(List *closures, Value *arg0) {
incRef((Value *)&_str_55);
return((Value *)&_str_55);
};


// --------- empty_impl main body --------------
Function fn_716 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_728}}};


// --------- count_impl --------------
Function fn_717;
Value *arityImpl_729(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_153(empty_list, arg0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_717 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_729}}};


// --------- conj_impl --------------
Function fn_718;
Value *arityImpl_730(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_212(empty_list, rslt1, (Value *)&protoFn_270);
Value *rslt3 = arityImpl_141(empty_list, rslt2);
Value *rslt4 = arityImpl_144(empty_list, rslt2);
Value *rslt5 = protoFnImpl_371(empty_list, rslt3, rslt4);
incRef(rslt5);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt5);
};


// --------- conj_impl main body --------------
Function fn_718 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_730}}};


// --------- reduce_impl --------------
Function fn_719;
Value *arityImpl_731(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_321(empty_list, rslt0, arg1, arg2);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- reduce_impl main body --------------
Function fn_719 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_731}}};


// --------- comp*_impl --------------
Function fn_720;

// --------- anon --------------
Function fn_733;
Value *arityImpl_734(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_153(empty_list, arg1);
Value *rslt1 = arityImpl_118(empty_list, arg0, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- anon main body --------------
Function fn_733 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_734}}};


// --------- anon --------------
Function fn_735;
Value *arityImpl_736(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt1 = arityImpl_165(empty_list, val0, arg0);
incRef((Value *)&_num_13);
dec_and_free(rslt1);
return((Value *)&_num_13);
};

Value *arityImpl_732(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt8);
Value *rslt1 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_668(empty_list, rslt1, (Value *)&protoFn_270);
Value *rslt4 = arityImpl_664(empty_list, rslt2, (Value *)&_num_13, (Value *)&fn_733);
Value *rslt5 = arityImpl_162(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_736;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_735 = malloc_function(1);
fn_735->type = FunctionType;
fn_735->name = "anon";
fn_735->arityCount = 1;
fn_735->arities[0] = arity_6;
Value *rslt7 = arityImpl_678(empty_list, rslt2, (Value *)fn_735);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free((Value *)fn_735);
dec_and_free(rslt7);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_720 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_732}}};


// --------- =*_impl --------------
Function fn_721;
Value *arityImpl_737(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_156(empty_list, arg0, arg1);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_721 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_737}}};


// --------- string-list_impl --------------
Function fn_722;
Value *arityImpl_738(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_722 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_738}}};


// --------- seq_impl --------------
Function fn_723;
Value *arityImpl_739(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_442(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt5);
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt2 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_343(empty_list, rslt2);
Value *rslt4 = arityImpl_132(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- seq_impl main body --------------
Function fn_723 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_739}}};


// --------- first_impl --------------
Function fn_724;
Value *arityImpl_740(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = arityImpl_442(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
} else {
dec_and_free(rslt3);
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt2 = protoImpl_564(empty_list, (Value *)&reified_567, rslt1);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- first_impl main body --------------
Function fn_724 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_740}}};


// --------- rest_impl --------------
Function fn_725;
Value *arityImpl_741(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_725 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_741}}};


// --------- sha1_impl --------------
Function fn_742;
Value *arityImpl_754(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_742 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_754}}};


// --------- empty?_impl --------------
Function fn_743;
Value *arityImpl_755(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_153(empty_list, arg0);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_13, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_743 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_755}}};


// --------- empty_impl --------------
Function fn_744;
Value *arityImpl_756(List *closures, Value *arg0) {
incRef((Value *)&_str_55);
return((Value *)&_str_55);
};


// --------- empty_impl main body --------------
Function fn_744 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_756}}};


// --------- count_impl --------------
Function fn_745;
Value *arityImpl_757(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_153(empty_list, arg0);
return(rslt0);
};


// --------- count_impl main body --------------
Function fn_745 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_757}}};


// --------- conj_impl --------------
Function fn_746;
Value *arityImpl_758(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = protoFnImpl_212(empty_list, rslt1, (Value *)&protoFn_270);
Value *rslt3 = arityImpl_141(empty_list, rslt2);
Value *rslt4 = arityImpl_144(empty_list, rslt2);
Value *rslt5 = protoFnImpl_371(empty_list, rslt3, rslt4);
incRef(rslt5);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt5);
};


// --------- conj_impl main body --------------
Function fn_746 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_758}}};


// --------- reduce_impl --------------
Function fn_747;
Value *arityImpl_759(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_321(empty_list, rslt0, arg1, arg2);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- reduce_impl main body --------------
Function fn_747 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_759}}};


// --------- comp*_impl --------------
Function fn_748;

// --------- anon --------------
Function fn_761;
Value *arityImpl_762(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_153(empty_list, arg1);
Value *rslt1 = arityImpl_118(empty_list, arg0, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- anon main body --------------
Function fn_761 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_762}}};


// --------- anon --------------
Function fn_763;
Value *arityImpl_764(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt1 = arityImpl_165(empty_list, val0, arg0);
incRef((Value *)&_num_13);
dec_and_free(rslt1);
return((Value *)&_num_13);
};

Value *arityImpl_760(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt8);
Value *rslt1 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_668(empty_list, rslt1, (Value *)&protoFn_270);
Value *rslt4 = arityImpl_664(empty_list, rslt2, (Value *)&_num_13, (Value *)&fn_761);
Value *rslt5 = arityImpl_162(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_764;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_763 = malloc_function(1);
fn_763->type = FunctionType;
fn_763->name = "anon";
fn_763->arityCount = 1;
fn_763->arities[0] = arity_6;
Value *rslt7 = arityImpl_678(empty_list, rslt2, (Value *)fn_763);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt1);
dec_and_free((Value *)fn_763);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- comp*_impl main body --------------
Function fn_748 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_760}}};


// --------- =*_impl --------------
Function fn_749;
Value *arityImpl_765(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_156(empty_list, arg0, arg1);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_749 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_765}}};


// --------- string-list_impl --------------
Function fn_750;
Value *arityImpl_766(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
return(rslt1);
};


// --------- string-list_impl main body --------------
Function fn_750 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_766}}};


// --------- seq_impl --------------
Function fn_751;
Value *arityImpl_767(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = arityImpl_442(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt5);
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt2 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
Value *rslt3 = protoFnImpl_343(empty_list, rslt2);
Value *rslt4 = arityImpl_132(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- seq_impl main body --------------
Function fn_751 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_767}}};


// --------- first_impl --------------
Function fn_752;
Value *arityImpl_768(List *closures, Value *arg0) {
Value *cond0;
Value *rslt3 = arityImpl_442(empty_list, arg0, (Value *)&_str_55);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef((Value *)&reified_487);
cond0 = (Value *)&reified_487;
} else {
dec_and_free(rslt3);
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt2 = protoImpl_564(empty_list, (Value *)&reified_567, rslt1);
incRef(rslt2);
cond0 = rslt2;
dec_and_free(rslt1);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- first_impl main body --------------
Function fn_752 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_768}}};


// --------- rest_impl --------------
Function fn_753;
Value *arityImpl_769(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
return(rslt0);
};


// --------- rest_impl main body --------------
Function fn_753 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_769}}};


// --------- str --------------
Function fn_770;

// --------- anon --------------
Function fn_772;
Value *arityImpl_773(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_153(empty_list, arg1);
Value *rslt1 = arityImpl_118(empty_list, arg0, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- anon main body --------------
Function fn_772 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_773}}};


// --------- anon --------------
Function fn_774;
Value *arityImpl_775(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt1 = arityImpl_165(empty_list, val0, arg0);
incRef((Value *)&_num_13);
dec_and_free(rslt1);
return((Value *)&_num_13);
};

Value *arityImpl_771(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *cond0;
Value *rslt7 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef((Value *)&_str_55);
cond0 = (Value *)&_str_55;
} else {
dec_and_free(rslt7);
Value *rslt1 = protoFnImpl_212(empty_list, arg0, (Value *)&protoFn_270);
Value *rslt3 = protoFnImpl_321(empty_list, rslt1, (Value *)&_num_13, (Value *)&fn_772);
Value *rslt4 = arityImpl_162(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = FnArityType;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_775;
incRef((Value *)rslt4);
arity_5->closures = listCons((Value *)rslt4, (List *)arity_5->closures);
Function *fn_774 = malloc_function(1);
fn_774->type = FunctionType;
fn_774->name = "anon";
fn_774->arityCount = 1;
fn_774->arities[0] = arity_5;
Value *rslt6 = protoFnImpl_261(empty_list, rslt1, (Value *)fn_774);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free((Value *)fn_774);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond0);
};

// --------- str main body --------------
Function fn_770 = {FunctionType, -1, "str", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_771}}};


// --------- take --------------
Function fn_777;
Value *arityImpl_778(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt6 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt6);
Value *rslt7 = arityImpl_442(empty_list, (Value *)&_num_13, arg1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt7);
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = protoFnImpl_341(empty_list, arg0);
Value *rslt3 = arityImpl_708(empty_list, arg1);
Value *rslt4 = arityImpl_778(closures, rslt2, rslt3);
Value *rslt5 = arityImpl_132(empty_list, rslt1, rslt4);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- take main body --------------
Function fn_777 = {FunctionType, -1, "take", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_778}}};


// --------- drop --------------
Function fn_780;
Value *arityImpl_781(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt4 = arityImpl_578(empty_list, arg1, (Value *)&_num_1);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt4);
Value *rslt1 = protoFnImpl_341(empty_list, arg0);
Value *rslt2 = arityImpl_708(empty_list, arg1);
Value *rslt3 = arityImpl_781(closures, rslt1, rslt2);
incRef(rslt3);
cond0 = rslt3;
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- drop main body --------------
Function fn_780 = {FunctionType, -1, "drop", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_781}}};


// --------- split --------------
Function fn_783;
Value *arityImpl_784(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt6 = protoFnImpl_319(empty_list, arg0);
Value *rslt7 = arityImpl_578(empty_list, arg1, (Value *)&_num_1);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
incRef((Value *)rslt6);
varArgs8 = (List *)listCons((Value *)rslt6, varArgs8);
Value *rslt9 = arityImpl_438(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
dec_and_free(rslt6);
dec_and_free(rslt7);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
Value *rslt10 = arityImpl_596(empty_list, arg2);
List *varArgs11 = empty_list;
incRef((Value *)arg0);
varArgs11 = (List *)listCons((Value *)arg0, varArgs11);
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
Value *rslt12 = arityImpl_253(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
incRef(rslt12);
cond0 = rslt12;
dec_and_free(rslt10);
dec_and_free(rslt12);
} else {
dec_and_free(rslt9);
Value *rslt1 = protoFnImpl_341(empty_list, arg0);
Value *rslt2 = arityImpl_708(empty_list, arg1);
Value *rslt3 = protoFnImpl_345(empty_list, arg0);
Value *rslt4 = arityImpl_132(empty_list, rslt3, arg2);
Value *rslt5 = arityImpl_784(closures, rslt1, rslt2, rslt4);
incRef(rslt5);
cond0 = rslt5;
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};

Value *arityImpl_785(List *closures, Value *arg0, Value *arg1) {
Value *rslt3;
FnArity *arity0 = findFnArity((Value *)&fn_783, 3);
if(arity0 != (FnArity *)0 && !arity0->variadic) {
FnType3 *fn2 = (FnType3 *)arity0->fn;
rslt3 = fn2(arity0->closures, arg0, arg1, var_129);
} else if(arity0 != (FnArity *)0 && arity0->variadic) {
FnType1 *fn2 = (FnType1 *)arity0->fn;
List *varArgs1 = empty_list;
incRef(var_129);
varArgs1 = (List *)listCons(var_129, varArgs1);
incRef(arg1);
varArgs1 = (List *)listCons(arg1, varArgs1);
incRef(arg0);
varArgs1 = (List *)listCons(arg0, varArgs1);
rslt3 = fn2(arity0->closures, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_783)->name);
  abort();
}
return(rslt3);
};


// --------- split main body --------------
Function fn_783 = {FunctionType, -1, "split", 2, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_784}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_785}}};


// --------- replace-at-nth --------------
Function fn_787;
Value *arityImpl_788(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt10 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt10);
Value *rslt11 = protoFnImpl_313(empty_list, arg0);
Value *rslt12 = arityImpl_708(empty_list, rslt11);
Value *rslt13 = arityImpl_578(empty_list, rslt12, arg1);
dec_and_free(rslt11);
dec_and_free(rslt12);

if (isTrue(rslt13)) {
dec_and_free(rslt13);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt13);
Value *rslt1 = arityImpl_785(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_345(empty_list, rslt1);
List *varArgs3 = empty_list;
incRef((Value *)arg2);
varArgs3 = (List *)listCons((Value *)arg2, varArgs3);
Value *rslt4 = arityImpl_253(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = arityImpl_353(empty_list, rslt1);
Value *rslt6 = protoFnImpl_341(empty_list, rslt5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
Value *rslt8 = arityImpl_253(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = protoFnImpl_371(empty_list, rslt2, rslt8);
incRef(rslt9);
cond0 = rslt9;
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- replace-at-nth main body --------------
Function fn_787 = {FunctionType, -1, "replace-at-nth", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_788}}};


// --------- remove-nth --------------
Function fn_790;
Value *arityImpl_791(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt8 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt8);
Value *rslt9 = protoFnImpl_313(empty_list, arg0);
Value *rslt10 = arityImpl_708(empty_list, rslt9);
Value *rslt11 = arityImpl_578(empty_list, rslt10, arg1);
dec_and_free(rslt10);
dec_and_free(rslt9);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt11);
Value *rslt1 = arityImpl_785(empty_list, arg0, arg1);
Value *rslt2 = protoFnImpl_345(empty_list, rslt1);
Value *rslt3 = arityImpl_353(empty_list, rslt1);
Value *rslt4 = protoFnImpl_341(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
Value *rslt6 = arityImpl_253(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_371(empty_list, rslt2, rslt6);
incRef(rslt7);
cond0 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- remove-nth main body --------------
Function fn_790 = {FunctionType, -1, "remove-nth", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_791}}};


// --------- partition --------------
Function fn_793;
Value *arityImpl_794(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_313(empty_list, arg0);
Value *rslt6 = arityImpl_578(empty_list, rslt5, arg1);
dec_and_free(rslt5);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt6);
Value *rslt1 = arityImpl_778(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_781(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_794(closures, rslt2, arg1);
Value *rslt4 = arityImpl_132(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- partition main body --------------
Function fn_793 = {FunctionType, -1, "partition", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_794}}};


// --------- partition-all --------------
Function fn_796;
Value *arityImpl_797(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_313(empty_list, arg0);
Value *rslt6 = arityImpl_578(empty_list, rslt5, arg1);
dec_and_free(rslt5);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
List *varArgs7 = empty_list;
incRef((Value *)arg0);
varArgs7 = (List *)listCons((Value *)arg0, varArgs7);
Value *rslt8 = arityImpl_253(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
incRef(rslt8);
cond0 = rslt8;
dec_and_free(rslt8);
} else {
dec_and_free(rslt6);
Value *rslt1 = arityImpl_778(empty_list, arg0, arg1);
Value *rslt2 = arityImpl_781(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_797(closures, rslt2, arg1);
Value *rslt4 = arityImpl_132(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- partition-all main body --------------
Function fn_796 = {FunctionType, -1, "partition-all", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_797}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_56 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_799;
Value *arityImpl_800(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_str_56);
varArgs6 = (List *)listCons((Value *)(Value *)&_str_56, varArgs6);
Value *rslt7 = arityImpl_697(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = arityImpl_96(empty_list);
incRef(rslt8);
cond0 = rslt8;
dec_and_free(rslt8);
dec_and_free(rslt7);
} else {
dec_and_free(rslt5);
Value *rslt9 = arityImpl_442(empty_list, arg1, (Value *)&_num_13);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
Value *rslt10 = protoFnImpl_343(empty_list, arg0);
Value *rslt11 = protoFnImpl_345(empty_list, rslt10);
incRef(rslt11);
cond0 = rslt11;
dec_and_free(rslt10);
dec_and_free(rslt11);
} else {
dec_and_free(rslt9);
Value *rslt1 = protoFnImpl_343(empty_list, arg0);
Value *rslt2 = protoFnImpl_341(empty_list, rslt1);
Value *rslt3 = arityImpl_708(empty_list, arg1);
Value *rslt4 = arityImpl_800(closures, rslt2, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
return(cond0);
};

Value *arityImpl_801(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt5 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(arg2);
cond0 = arg2;
} else {
dec_and_free(rslt5);
Value *rslt6 = arityImpl_442(empty_list, arg1, (Value *)&_num_13);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *rslt7 = protoFnImpl_343(empty_list, arg0);
Value *rslt8 = protoFnImpl_345(empty_list, rslt7);
incRef(rslt8);
cond0 = rslt8;
dec_and_free(rslt8);
dec_and_free(rslt7);
} else {
dec_and_free(rslt6);
Value *rslt1 = protoFnImpl_343(empty_list, arg0);
Value *rslt2 = protoFnImpl_341(empty_list, rslt1);
Value *rslt3 = arityImpl_708(empty_list, arg1);
Value *rslt4 = arityImpl_801(closures, rslt2, rslt3, arg2);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- nth main body --------------
Function fn_799 = {FunctionType, -1, "nth", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_800}, &(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_801}}};


// --------- last --------------
Function fn_803;
Value *arityImpl_804(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_313(empty_list, arg0);
Value *rslt1 = arityImpl_708(empty_list, rslt0);
Value *rslt2 = arityImpl_800(empty_list, arg0, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- last main body --------------
Function fn_803 = {FunctionType, -1, "last", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_804}}};


// --------- butlast --------------
Function fn_806;
Value *arityImpl_807(List *closures, Value *arg0) {
Value *cond0;
Value *rslt5 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt5);
Value *rslt6 = protoFnImpl_313(empty_list, arg0);
Value *rslt7 = arityImpl_442(empty_list, (Value *)&_num_1, rslt6);
dec_and_free(rslt6);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt7);
Value *rslt1 = protoFnImpl_345(empty_list, arg0);
Value *rslt2 = protoFnImpl_341(empty_list, arg0);
Value *rslt3 = arityImpl_807(closures, rslt2);
Value *rslt4 = arityImpl_132(empty_list, rslt1, rslt3);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- butlast main body --------------
Function fn_806 = {FunctionType, -1, "butlast", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_807}}};


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
Value *var_809 = (Value *)&emptyBMI;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_57 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_59 = {1, -1, 1,"}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_58 = {1, -1, 1,"{"};

// --------- count_impl --------------
Function fn_810;
Value *arityImpl_823(List *closures, Value *arg0) {

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
Function fn_810 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_823}}};


// --------- empty?_impl --------------
Function fn_811;
Value *arityImpl_824(List *closures, Value *arg0) {

if (((BitmapIndexedNode *)arg0)->bitmap == 0)
   return(true);
else
   return(false);
};


// --------- empty?_impl main body --------------
Function fn_811 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_824}}};


// --------- zero_impl --------------
Function fn_812;
Value *arityImpl_825(List *closures, Value *arg0) {
incRef(var_809);
return(var_809);
};


// --------- zero_impl main body --------------
Function fn_812 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_825}}};


// --------- comp*_impl --------------
Function fn_813;

// --------- anon --------------
Function fn_827;

// --------- anon --------------
Function fn_829;
Value *arityImpl_830(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = arityImpl_605(empty_list, (Value *)&protoFn_401, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_829 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_830}}};

Value *arityImpl_828(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_343(empty_list, arg1);
Value *rslt2 = protoFnImpl_321(empty_list, rslt0, arg0, (Value *)&fn_829);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_827 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_828}}};

Value *arityImpl_826(List *closures, Value *arg0, Value *arg1) {
Value *rslt1 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_827);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_813 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_826}}};


// --------- get_impl --------------
Function fn_814;
Value *arityImpl_831(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_814 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_831}}};


// --------- keys_impl --------------
Function fn_815;
Value *arityImpl_832(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_261(empty_list, rslt0, (Value *)&protoFn_333);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- keys_impl main body --------------
Function fn_815 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_832}}};


// --------- vals_impl --------------
Function fn_816;
Value *arityImpl_833(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_261(empty_list, rslt0, (Value *)&fn_352);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- vals_impl main body --------------
Function fn_816 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_833}}};


// --------- assoc_impl --------------
Function fn_817;
Value *arityImpl_834(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_817 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_834}}};


// --------- string-list_impl --------------
Function fn_818;

// --------- anon --------------
Function fn_836;
Value *arityImpl_837(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_261(empty_list, arg0, (Value *)&protoFn_270);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_52, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_680(empty_list, rslt0, rslt2);
Value *rslt4 = arityImpl_141(empty_list, rslt3);
Value *rslt5 = arityImpl_144(empty_list, rslt3);
Value *rslt6 = protoFnImpl_371(empty_list, rslt4, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt6);
};


// --------- anon main body --------------
Function fn_836 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_837}}};

Value *arityImpl_835(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *cond1;
Value *rslt17 = arityImpl_138(empty_list, rslt0);

if (isTrue(rslt17)) {
dec_and_free(rslt17);
List *varArgs18 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs18 = (List *)listCons((Value *)(Value *)&_str_57, varArgs18);
Value *rslt19 = arityImpl_253(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
incRef(rslt19);
cond1 = rslt19;
dec_and_free(rslt19);
} else {
dec_and_free(rslt17);
Value *rslt3 = protoFnImpl_261(empty_list, rslt0, (Value *)&fn_836);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_50, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
Value *rslt6 = arityImpl_680(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_141(empty_list, rslt6);
Value *rslt8 = arityImpl_144(empty_list, rslt6);
Value *rslt9 = protoFnImpl_371(empty_list, rslt7, rslt8);
List *varArgs10 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs10 = (List *)listCons((Value *)(Value *)&_str_58, varArgs10);
Value *rslt11 = arityImpl_253(empty_list, (Value *)varArgs10);
dec_and_free((Value *)varArgs10);
List *varArgs12 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs12 = (List *)listCons((Value *)(Value *)&_str_59, varArgs12);
Value *rslt13 = arityImpl_253(empty_list, (Value *)varArgs12);
dec_and_free((Value *)varArgs12);
List *varArgs14 = empty_list;
incRef((Value *)rslt13);
varArgs14 = (List *)listCons((Value *)rslt13, varArgs14);
incRef((Value *)rslt9);
varArgs14 = (List *)listCons((Value *)rslt9, varArgs14);
Value *rslt15 = arityImpl_253(empty_list, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
Value *rslt16 = protoFnImpl_371(empty_list, rslt11, rslt15);
incRef(rslt16);
cond1 = rslt16;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt15);
dec_and_free(rslt13);
dec_and_free(rslt11);
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt16);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};


// --------- string-list_impl main body --------------
Function fn_818 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_835}}};


// --------- seq_impl --------------
Function fn_819;
Value *arityImpl_838(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_398(empty_list, arg0, var_129);
return(rslt0);
};


// --------- seq_impl main body --------------
Function fn_819 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_838}}};


// --------- hash-seq_impl --------------
Function fn_820;
Value *arityImpl_839(List *closures, Value *arg0, Value *arg1) {

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
Function fn_820 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_839}}};


// --------- assoc*_impl --------------
Function fn_821;
Value *arityImpl_840(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_821 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_840}}};


// --------- get*_impl --------------
Function fn_822;
Value *arityImpl_841(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_822 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_841}}};


// --------- count_impl --------------
Function fn_842;
Value *arityImpl_855(List *closures, Value *arg0) {

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
Function fn_842 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_855}}};


// --------- empty?_impl --------------
Function fn_843;
Value *arityImpl_856(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};


// --------- empty?_impl main body --------------
Function fn_843 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_856}}};


// --------- zero_impl --------------
Function fn_844;
Value *arityImpl_857(List *closures, Value *arg0) {
incRef(var_809);
return(var_809);
};


// --------- zero_impl main body --------------
Function fn_844 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_857}}};


// --------- comp*_impl --------------
Function fn_845;

// --------- anon --------------
Function fn_859;

// --------- anon --------------
Function fn_861;
Value *arityImpl_862(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = arityImpl_605(empty_list, (Value *)&protoFn_401, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_861 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_862}}};

Value *arityImpl_860(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_343(empty_list, arg1);
Value *rslt2 = protoFnImpl_321(empty_list, rslt0, arg0, (Value *)&fn_861);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_859 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_860}}};

Value *arityImpl_858(List *closures, Value *arg0, Value *arg1) {
Value *rslt1 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_859);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_845 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_858}}};


// --------- get_impl --------------
Function fn_846;
Value *arityImpl_863(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_846 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_863}}};


// --------- keys_impl --------------
Function fn_847;
Value *arityImpl_864(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_261(empty_list, rslt0, (Value *)&protoFn_333);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- keys_impl main body --------------
Function fn_847 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_864}}};


// --------- vals_impl --------------
Function fn_848;
Value *arityImpl_865(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_261(empty_list, rslt0, (Value *)&fn_352);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- vals_impl main body --------------
Function fn_848 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_865}}};


// --------- assoc_impl --------------
Function fn_849;
Value *arityImpl_866(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_849 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_866}}};


// --------- string-list_impl --------------
Function fn_850;

// --------- anon --------------
Function fn_868;
Value *arityImpl_869(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_261(empty_list, arg0, (Value *)&protoFn_270);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_52, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_680(empty_list, rslt0, rslt2);
Value *rslt4 = arityImpl_141(empty_list, rslt3);
Value *rslt5 = arityImpl_144(empty_list, rslt3);
Value *rslt6 = protoFnImpl_371(empty_list, rslt4, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt6);
};


// --------- anon main body --------------
Function fn_868 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_869}}};

Value *arityImpl_867(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *cond1;
Value *rslt17 = arityImpl_138(empty_list, rslt0);

if (isTrue(rslt17)) {
dec_and_free(rslt17);
List *varArgs18 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs18 = (List *)listCons((Value *)(Value *)&_str_57, varArgs18);
Value *rslt19 = arityImpl_253(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
incRef(rslt19);
cond1 = rslt19;
dec_and_free(rslt19);
} else {
dec_and_free(rslt17);
Value *rslt3 = protoFnImpl_261(empty_list, rslt0, (Value *)&fn_868);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_50, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
Value *rslt6 = arityImpl_680(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_141(empty_list, rslt6);
Value *rslt8 = arityImpl_144(empty_list, rslt6);
Value *rslt9 = protoFnImpl_371(empty_list, rslt7, rslt8);
List *varArgs10 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs10 = (List *)listCons((Value *)(Value *)&_str_58, varArgs10);
Value *rslt11 = arityImpl_253(empty_list, (Value *)varArgs10);
dec_and_free((Value *)varArgs10);
List *varArgs12 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs12 = (List *)listCons((Value *)(Value *)&_str_59, varArgs12);
Value *rslt13 = arityImpl_253(empty_list, (Value *)varArgs12);
dec_and_free((Value *)varArgs12);
List *varArgs14 = empty_list;
incRef((Value *)rslt13);
varArgs14 = (List *)listCons((Value *)rslt13, varArgs14);
incRef((Value *)rslt9);
varArgs14 = (List *)listCons((Value *)rslt9, varArgs14);
Value *rslt15 = arityImpl_253(empty_list, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
Value *rslt16 = protoFnImpl_371(empty_list, rslt11, rslt15);
incRef(rslt16);
cond1 = rslt16;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt15);
dec_and_free(rslt13);
dec_and_free(rslt11);
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt16);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};


// --------- string-list_impl main body --------------
Function fn_850 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_867}}};


// --------- seq_impl --------------
Function fn_851;
Value *arityImpl_870(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_398(empty_list, arg0, var_129);
return(rslt0);
};


// --------- seq_impl main body --------------
Function fn_851 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_870}}};


// --------- hash-seq_impl --------------
Function fn_852;
Value *arityImpl_871(List *closures, Value *arg0, Value *arg1) {

ArrayNode *node = (ArrayNode *)arg0;
List *seq = (List *)arg1;
for (int i = 0; i < 32; i++) {
   if (node->array[i] != (Value *)0)
     seq = (List *)hashSeq(node->array[i], (Value *)seq);
}
return((Value *)seq);
};


// --------- hash-seq_impl main body --------------
Function fn_852 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_871}}};


// --------- assoc*_impl --------------
Function fn_853;
Value *arityImpl_872(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_853 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_872}}};


// --------- get*_impl --------------
Function fn_854;
Value *arityImpl_873(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_854 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_873}}};


// --------- count_impl --------------
Function fn_874;
Value *arityImpl_887(List *closures, Value *arg0) {

return(numberValue(((HashCollisionNode *) arg0)->count / 2));
};


// --------- count_impl main body --------------
Function fn_874 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_887}}};


// --------- empty?_impl --------------
Function fn_875;
Value *arityImpl_888(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};


// --------- empty?_impl main body --------------
Function fn_875 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_888}}};


// --------- zero_impl --------------
Function fn_876;
Value *arityImpl_889(List *closures, Value *arg0) {
incRef(var_809);
return(var_809);
};


// --------- zero_impl main body --------------
Function fn_876 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_889}}};


// --------- comp*_impl --------------
Function fn_877;

// --------- anon --------------
Function fn_891;

// --------- anon --------------
Function fn_893;
Value *arityImpl_894(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = arityImpl_605(empty_list, (Value *)&protoFn_401, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_893 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_894}}};

Value *arityImpl_892(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_343(empty_list, arg1);
Value *rslt2 = protoFnImpl_321(empty_list, rslt0, arg0, (Value *)&fn_893);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_891 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_892}}};

Value *arityImpl_890(List *closures, Value *arg0, Value *arg1) {
Value *rslt1 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_891);
return(rslt1);
};


// --------- comp*_impl main body --------------
Function fn_877 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_890}}};


// --------- get_impl --------------
Function fn_878;
Value *arityImpl_895(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_878 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_895}}};


// --------- keys_impl --------------
Function fn_879;
Value *arityImpl_896(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_261(empty_list, rslt0, (Value *)&protoFn_333);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- keys_impl main body --------------
Function fn_879 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_896}}};


// --------- vals_impl --------------
Function fn_880;
Value *arityImpl_897(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *rslt1 = protoFnImpl_261(empty_list, rslt0, (Value *)&fn_352);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- vals_impl main body --------------
Function fn_880 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_897}}};


// --------- assoc_impl --------------
Function fn_881;
Value *arityImpl_898(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_881 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_898}}};


// --------- string-list_impl --------------
Function fn_882;

// --------- anon --------------
Function fn_900;
Value *arityImpl_901(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_261(empty_list, arg0, (Value *)&protoFn_270);
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_52, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_680(empty_list, rslt0, rslt2);
Value *rslt4 = arityImpl_141(empty_list, rslt3);
Value *rslt5 = arityImpl_144(empty_list, rslt3);
Value *rslt6 = protoFnImpl_371(empty_list, rslt4, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt6);
};


// --------- anon main body --------------
Function fn_900 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_901}}};

Value *arityImpl_899(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_343(empty_list, arg0);
Value *cond1;
Value *rslt17 = arityImpl_138(empty_list, rslt0);

if (isTrue(rslt17)) {
dec_and_free(rslt17);
List *varArgs18 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs18 = (List *)listCons((Value *)(Value *)&_str_57, varArgs18);
Value *rslt19 = arityImpl_253(empty_list, (Value *)varArgs18);
dec_and_free((Value *)varArgs18);
incRef(rslt19);
cond1 = rslt19;
dec_and_free(rslt19);
} else {
dec_and_free(rslt17);
Value *rslt3 = protoFnImpl_261(empty_list, rslt0, (Value *)&fn_900);
List *varArgs4 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs4 = (List *)listCons((Value *)(Value *)&_str_50, varArgs4);
Value *rslt5 = arityImpl_253(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
Value *rslt6 = arityImpl_680(empty_list, rslt3, rslt5);
Value *rslt7 = arityImpl_141(empty_list, rslt6);
Value *rslt8 = arityImpl_144(empty_list, rslt6);
Value *rslt9 = protoFnImpl_371(empty_list, rslt7, rslt8);
List *varArgs10 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs10 = (List *)listCons((Value *)(Value *)&_str_58, varArgs10);
Value *rslt11 = arityImpl_253(empty_list, (Value *)varArgs10);
dec_and_free((Value *)varArgs10);
List *varArgs12 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs12 = (List *)listCons((Value *)(Value *)&_str_59, varArgs12);
Value *rslt13 = arityImpl_253(empty_list, (Value *)varArgs12);
dec_and_free((Value *)varArgs12);
List *varArgs14 = empty_list;
incRef((Value *)rslt13);
varArgs14 = (List *)listCons((Value *)rslt13, varArgs14);
incRef((Value *)rslt9);
varArgs14 = (List *)listCons((Value *)rslt9, varArgs14);
Value *rslt15 = arityImpl_253(empty_list, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
Value *rslt16 = protoFnImpl_371(empty_list, rslt11, rslt15);
incRef(rslt16);
cond1 = rslt16;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt15);
dec_and_free(rslt13);
dec_and_free(rslt11);
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt16);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};


// --------- string-list_impl main body --------------
Function fn_882 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_899}}};


// --------- seq_impl --------------
Function fn_883;
Value *arityImpl_902(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_398(empty_list, arg0, var_129);
return(rslt0);
};


// --------- seq_impl main body --------------
Function fn_883 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_902}}};


// --------- hash-seq_impl --------------
Function fn_884;
Value *arityImpl_903(List *closures, Value *arg0, Value *arg1) {

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
Function fn_884 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_903}}};


// --------- assoc*_impl --------------
Function fn_885;
Value *arityImpl_904(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_885 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_904}}};


// --------- get*_impl --------------
Function fn_886;
Value *arityImpl_905(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_886 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_905}}};


// --------- hash-map --------------
Function fn_906;

// --------- anon --------------
Function fn_908;
Value *arityImpl_909(List *closures, Value *arg0, Value *arg1) {
List *varArgs0 = empty_list;
incRef((Value *)arg1);
varArgs0 = (List *)listCons((Value *)arg1, varArgs0);
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
Value *rslt1 = arityImpl_253(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = arityImpl_605(empty_list, (Value *)&protoFn_401, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- anon main body --------------
Function fn_908 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_909}}};

Value *arityImpl_907(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt0 = arityImpl_794(empty_list, arg0, (Value *)&_num_2);
Value *rslt2 = protoFnImpl_321(empty_list, rslt0, var_809, (Value *)&fn_908);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};

// --------- hash-map main body --------------
Function fn_906 = {FunctionType, -1, "hash-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_907}}};


// --------- =*_impl --------------
Function fn_912;
Value *arityImpl_913(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_99(empty_list, arg0);
Value *rslt1 = arityImpl_99(empty_list, arg1);
Value *rslt2 = arityImpl_442(empty_list, rslt0, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_912 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_913}}};

Value *protoImpl_914(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_911 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_914}}};

ReifiedVal reified_915 = {17, -1, 1, {(Value *)&fn_912}};

// --------- merge-with --------------
Function fn_917;

// --------- anon --------------
Function fn_919;

// --------- anon --------------
Function fn_921;
Value *arityImpl_922(List *closures, Value *arg0, Value *arg3) {
Value * val2  = closures->head;
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
Value *rslt0 = protoFnImpl_422(empty_list, arg0, arg1, (Value *)&reified_915);
Value *cond1;
Value *rslt8 = arityImpl_442(empty_list, (Value *)&reified_915, rslt0);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
Value *rslt9 = protoFnImpl_415(empty_list, arg0, arg1, arg2);
incRef(rslt9);
cond1 = rslt9;
dec_and_free(rslt9);
} else {
dec_and_free(rslt8);
Value *rslt6;
if((val2)->type != FunctionType) {
rslt6 = protoFnImpl_13(empty_list, val2, rslt0, arg2);
} else {
FnArity *arity3 = findFnArity(val2, 2);
if(arity3 != (FnArity *)0 && !arity3->variadic) {
FnType2 *fn5 = (FnType2 *)arity3->fn;
rslt6 = fn5(arity3->closures, rslt0, arg2);
} else if(arity3 != (FnArity *)0 && arity3->variadic) {
FnType1 *fn5 = (FnType1 *)arity3->fn;
List *varArgs4 = empty_list;
incRef(arg2);
varArgs4 = (List *)listCons(arg2, varArgs4);
incRef(rslt0);
varArgs4 = (List *)listCons(rslt0, varArgs4);
rslt6 = fn5(arity3->closures, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val2)->name);
  abort();
}
}
Value *rslt7 = protoFnImpl_415(empty_list, arg0, arg1, rslt6);
incRef(rslt7);
cond1 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};

Value *arityImpl_920(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt0 = protoFnImpl_343(empty_list, arg1);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = FnArityType;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_922;
incRef((Value *)val2);
arity_1->closures = listCons((Value *)val2, (List *)arity_1->closures);
Function *fn_921 = malloc_function(1);
fn_921->type = FunctionType;
fn_921->name = "anon";
fn_921->arityCount = 1;
fn_921->arities[0] = arity_1;
Value *rslt3 = protoFnImpl_321(empty_list, rslt0, arg0, (Value *)fn_921);
incRef(rslt3);
dec_and_free((Value *)fn_921);
dec_and_free(rslt0);
dec_and_free(rslt3);
return(rslt3);
};

Value *arityImpl_918(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *) argsList;
Value *cond0;
Value *rslt3 = arityImpl_138(empty_list, arg2);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
incRef(arg1);
cond0 = arg1;
} else {
dec_and_free(rslt3);
FnArity *arity_1 = malloc_fnArity();
arity_1->type = FnArityType;
arity_1->count = 2;
arity_1->closures = empty_list;
arity_1->variadic = 0;
arity_1->fn = arityImpl_920;
incRef((Value *)arg0);
arity_1->closures = listCons((Value *)arg0, (List *)arity_1->closures);
Function *fn_919 = malloc_function(1);
fn_919->type = FunctionType;
fn_919->name = "anon";
fn_919->arityCount = 1;
fn_919->arities[0] = arity_1;
Value *rslt2 = protoFnImpl_321(empty_list, arg2, arg1, (Value *)fn_919);
incRef(rslt2);
cond0 = rslt2;
dec_and_free((Value *)fn_919);
dec_and_free(rslt2);
}
return(cond0);
};

// --------- merge-with main body --------------
Function fn_917 = {FunctionType, -1, "merge-with", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_918}}};

SubString _kw_2 = {5, -1, 17, 0, 0, ":get-in-not-found"};

// --------- get-in --------------
Function fn_924;
Value *arityImpl_925(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt7 = protoFnImpl_313(empty_list, arg1);
Value *rslt8 = arityImpl_442(empty_list, rslt7, (Value *)&_num_13);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(arg2);
cond0 = arg2;
} else {
dec_and_free(rslt8);
Value *rslt9 = protoFnImpl_313(empty_list, arg1);
Value *rslt10 = arityImpl_442(empty_list, rslt9, (Value *)&_num_1);
dec_and_free(rslt9);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
Value *rslt11 = protoFnImpl_345(empty_list, arg1);
Value *rslt12 = protoFnImpl_422(empty_list, arg0, rslt11, arg2);
incRef(rslt12);
cond0 = rslt12;
dec_and_free(rslt11);
dec_and_free(rslt12);
} else {
dec_and_free(rslt10);
Value *rslt1 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = protoFnImpl_422(empty_list, arg0, rslt1, (Value *)&_kw_2);
Value *cond3;
Value *rslt6 = arityImpl_442(empty_list, (Value *)&_kw_2, rslt2);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(arg2);
cond3 = arg2;
} else {
dec_and_free(rslt6);
Value *rslt4 = protoFnImpl_341(empty_list, arg1);
Value *rslt5 = arityImpl_925(closures, rslt2, rslt4, arg2);
incRef(rslt5);
cond3 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
incRef(cond3);
cond0 = cond3;
dec_and_free(rslt1);
dec_and_free(cond3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- get-in main body --------------
Function fn_924 = {FunctionType, -1, "get-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_925}}};

SubString _kw_3 = {5, -1, 14, 0, 0, ":update-in-nil"};

// --------- update-in --------------
Function fn_927;
Value *arityImpl_928(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt8 = protoFnImpl_313(empty_list, arg1);
Value *rslt9 = arityImpl_442(empty_list, rslt8, (Value *)&_num_13);
dec_and_free(rslt8);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt9);
Value *rslt10 = protoFnImpl_313(empty_list, arg1);
Value *rslt11 = arityImpl_442(empty_list, rslt10, (Value *)&_num_1);
dec_and_free(rslt10);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
Value *rslt12 = protoFnImpl_345(empty_list, arg1);
Value *rslt13 = protoFnImpl_422(empty_list, arg0, rslt12, (Value *)&_kw_3);
Value *cond14;
Value *rslt20 = arityImpl_442(empty_list, (Value *)&_kw_3, rslt13);

if (isTrue(rslt20)) {
dec_and_free(rslt20);
incRef(arg0);
cond14 = arg0;
} else {
dec_and_free(rslt20);
Value *rslt18;
if((arg2)->type != FunctionType) {
rslt18 = protoFnImpl_11(empty_list, arg2, rslt13);
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
dec_and_free((Value *)varArgs16);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg2)->name);
  abort();
}
}
Value *rslt19 = protoFnImpl_415(empty_list, arg0, rslt12, rslt18);
incRef(rslt19);
cond14 = rslt19;
dec_and_free(rslt19);
dec_and_free(rslt18);
}
incRef(cond14);
cond0 = cond14;
dec_and_free(cond14);
dec_and_free(rslt13);
dec_and_free(rslt12);
} else {
dec_and_free(rslt11);
Value *rslt1 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = protoFnImpl_422(empty_list, arg0, rslt1, (Value *)&_kw_3);
Value *cond3;
Value *rslt7 = arityImpl_442(empty_list, (Value *)&_kw_3, rslt2);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(arg0);
cond3 = arg0;
} else {
dec_and_free(rslt7);
Value *rslt4 = protoFnImpl_341(empty_list, arg1);
Value *rslt5 = arityImpl_928(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_415(empty_list, arg0, rslt1, rslt5);
incRef(rslt6);
cond3 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
}
incRef(cond3);
cond0 = cond3;
dec_and_free(rslt1);
dec_and_free(cond3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- update-in main body --------------
Function fn_927 = {FunctionType, -1, "update-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_928}}};

SubString _kw_4 = {5, -1, 13, 0, 0, ":assoc-in-nil"};

// --------- assoc-in --------------
Function fn_930;
Value *arityImpl_931(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond0;
Value *rslt13 = protoFnImpl_313(empty_list, arg1);
Value *rslt14 = arityImpl_442(empty_list, rslt13, (Value *)&_num_13);
dec_and_free(rslt13);

if (isTrue(rslt14)) {
dec_and_free(rslt14);
incRef(arg0);
cond0 = arg0;
} else {
dec_and_free(rslt14);
Value *rslt15 = protoFnImpl_313(empty_list, arg1);
Value *rslt16 = arityImpl_442(empty_list, rslt15, (Value *)&_num_1);
dec_and_free(rslt15);

if (isTrue(rslt16)) {
dec_and_free(rslt16);
Value *rslt17 = protoFnImpl_345(empty_list, arg1);
Value *rslt18 = protoFnImpl_415(empty_list, arg0, rslt17, arg2);
incRef(rslt18);
cond0 = rslt18;
dec_and_free(rslt18);
dec_and_free(rslt17);
} else {
dec_and_free(rslt16);
Value *rslt1 = protoFnImpl_345(empty_list, arg1);
Value *rslt2 = protoFnImpl_422(empty_list, arg0, rslt1, (Value *)&_kw_4);
Value *cond3;
Value *rslt7 = arityImpl_442(empty_list, (Value *)&_kw_4, rslt2);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
List *varArgs8 = empty_list;
Value *rslt9 = arityImpl_907(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_341(empty_list, arg1);
Value *rslt11 = arityImpl_931(closures, rslt9, rslt10, arg2);
Value *rslt12 = protoFnImpl_415(empty_list, arg0, rslt1, rslt11);
incRef(rslt12);
cond3 = rslt12;
dec_and_free(rslt10);
dec_and_free(rslt11);
dec_and_free(rslt9);
dec_and_free(rslt12);
} else {
dec_and_free(rslt7);
Value *rslt4 = protoFnImpl_341(empty_list, arg1);
Value *rslt5 = arityImpl_931(closures, rslt2, rslt4, arg2);
Value *rslt6 = protoFnImpl_415(empty_list, arg0, rslt1, rslt5);
incRef(rslt6);
cond3 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
}
incRef(cond3);
cond0 = cond3;
dec_and_free(rslt1);
dec_and_free(cond3);
dec_and_free(rslt2);
}
}
return(cond0);
};


// --------- assoc-in main body --------------
Function fn_930 = {FunctionType, -1, "assoc-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_931}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[19];} _str_60 = {1, -1, 18,"Could not look up "};

// --------- sha1_impl --------------
Function fn_933;
Value *arityImpl_938(List *closures, Value *arg0) {

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
Function fn_933 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_938}}};


// --------- =*_impl --------------
Function fn_934;
Value *arityImpl_939(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_159(empty_list, arg0, arg1);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_934 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_939}}};


// --------- string-list_impl --------------
Function fn_935;
Value *arityImpl_940(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_267(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_935 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_940}}};


// --------- invoke_impl --------------
Function fn_936;
Value *arityImpl_941(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_422(empty_list, arg1, arg0, (Value *)&reified_915);
Value *cond1;
Value *rslt2 = arityImpl_442(empty_list, (Value *)&reified_915, rslt0);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_60);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_60, varArgs3);
Value *rslt4 = arityImpl_697(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
cond1 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
} else {
dec_and_free(rslt2);
incRef(rslt0);
cond1 = rslt0;
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};


// --------- invoke_impl main body --------------
Function fn_936 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_941}}};


// --------- name_impl --------------
Function fn_937;
Value *arityImpl_942(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_84(empty_list, arg0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_937 = {FunctionType, -1, "name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_942}}};


// --------- sha1_impl --------------
Function fn_943;
Value *arityImpl_949(List *closures, Value *arg0) {

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
Function fn_943 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_949}}};


// --------- =*_impl --------------
Function fn_944;
Value *arityImpl_950(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = arityImpl_159(empty_list, arg0, arg1);
return(rslt0);
};


// --------- =*_impl main body --------------
Function fn_944 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_950}}};


// --------- string-list_impl --------------
Function fn_945;
Value *arityImpl_951(List *closures, Value *arg0) {
Value *rslt0 = protoFnImpl_267(empty_list, arg0);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
Value *rslt2 = arityImpl_253(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
incRef(rslt2);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_945 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_951}}};


// --------- invoke_impl --------------
Function fn_946;
Value *arityImpl_952(List *closures, Value *arg0, Value *arg1) {
Value *rslt0 = protoFnImpl_422(empty_list, arg1, arg0, (Value *)&reified_915);
Value *cond1;
Value *rslt2 = arityImpl_442(empty_list, (Value *)&reified_915, rslt0);

if (isTrue(rslt2)) {
dec_and_free(rslt2);
List *varArgs3 = empty_list;
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
incRef((Value *)(Value *)&_str_60);
varArgs3 = (List *)listCons((Value *)(Value *)&_str_60, varArgs3);
Value *rslt4 = arityImpl_697(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = arityImpl_96(empty_list);
incRef(rslt5);
cond1 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
} else {
dec_and_free(rslt2);
incRef(rslt0);
cond1 = rslt0;
}
incRef(cond1);
dec_and_free(cond1);
dec_and_free(rslt0);
return(cond1);
};


// --------- invoke_impl main body --------------
Function fn_946 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_952}}};


// --------- invoke_impl --------------
Function fn_947;
Value *arityImpl_953(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt0 = protoFnImpl_422(empty_list, arg1, arg0, arg2);
return(rslt0);
};


// --------- invoke_impl main body --------------
Function fn_947 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_953}}};


// --------- name_impl --------------
Function fn_948;
Value *arityImpl_954(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_84(empty_list, arg0);
return(rslt0);
};


// --------- name_impl main body --------------
Function fn_948 = {FunctionType, -1, "name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_954}}};


// --------- symbol? --------------
Function fn_955;
Value *arityImpl_956(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_99(empty_list, arg0);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_7, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- symbol? main body --------------
Function fn_955 = {FunctionType, -1, "symbol?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_956}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_61 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_958;
Value *arityImpl_959(List *closures, Value *arg0) {
List *varArgs0 = empty_list;
incRef((Value *)arg0);
varArgs0 = (List *)listCons((Value *)arg0, varArgs0);
incRef((Value *)(Value *)&_str_61);
varArgs0 = (List *)listCons((Value *)(Value *)&_str_61, varArgs0);
Value *rslt1 = arityImpl_771(empty_list, (Value *)varArgs0);
dec_and_free((Value *)varArgs0);
Value *rslt2 = arityImpl_93(empty_list, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keyword main body --------------
Function fn_958 = {FunctionType, -1, "keyword", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_959}}};


// --------- keyword? --------------
Function fn_961;
Value *arityImpl_962(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_99(empty_list, arg0);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_5, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- keyword? main body --------------
Function fn_961 = {FunctionType, -1, "keyword?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_962}}};


// --------- number? --------------
Function fn_964;
Value *arityImpl_965(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_99(empty_list, arg0);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_2, rslt0);
incRef(rslt1);
dec_and_free(rslt1);
dec_and_free(rslt0);
return(rslt1);
};


// --------- number? main body --------------
Function fn_964 = {FunctionType, -1, "number?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_965}}};


// --------- string? --------------
Function fn_967;
Value *arityImpl_968(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_99(empty_list, arg0);
Value *rslt1 = arityImpl_442(empty_list, (Value *)&_num_1, rslt0);
Value *rslt2 = arityImpl_99(empty_list, arg0);
Value *rslt3 = arityImpl_442(empty_list, (Value *)&_num_6, rslt2);
List *varArgs4 = empty_list;
incRef((Value *)rslt3);
varArgs4 = (List *)listCons((Value *)rslt3, varArgs4);
incRef((Value *)rslt1);
varArgs4 = (List *)listCons((Value *)rslt1, varArgs4);
Value *rslt5 = arityImpl_438(empty_list, (Value *)varArgs4);
dec_and_free((Value *)varArgs4);
incRef(rslt5);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt5);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt5);
};


// --------- string? main body --------------
Function fn_967 = {FunctionType, -1, "string?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_968}}};


// --------- range* --------------
Function fn_970;
Value *arityImpl_971(List *closures, Value *arg0) {
Value *cond0;
Value *rslt4 = arityImpl_442(empty_list, (Value *)&_num_13, arg0);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_num_13);
varArgs5 = (List *)listCons((Value *)(Value *)&_num_13, varArgs5);
Value *rslt6 = arityImpl_253(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
incRef(rslt6);
cond0 = rslt6;
dec_and_free(rslt6);
} else {
dec_and_free(rslt4);
Value *rslt1 = arityImpl_708(empty_list, arg0);
Value *rslt2 = arityImpl_971(closures, rslt1);
Value *rslt3 = arityImpl_132(empty_list, arg0, rslt2);
incRef(rslt3);
cond0 = rslt3;
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- range* main body --------------
Function fn_970 = {FunctionType, -1, "range*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_971}}};


// --------- range --------------
Function fn_973;
Value *arityImpl_974(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_708(empty_list, arg0);
Value *rslt1 = arityImpl_971(empty_list, rslt0);
Value *rslt2 = arityImpl_596(empty_list, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt0);
dec_and_free(rslt2);
return(rslt2);
};


// --------- range main body --------------
Function fn_973 = {FunctionType, -1, "range", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_974}}};


// --------- repeat --------------
Function fn_976;

// --------- anon --------------
Function fn_978;
Value *arityImpl_979(List *closures, Value *arg0) {
Value * val0  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val0);
return(val0);
};

Value *arityImpl_977(List *closures, Value *arg0, Value *arg1) {
Value *cond0;
Value *rslt5 = arityImpl_578(empty_list, arg0, (Value *)&_num_1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef(var_129);
cond0 = var_129;
} else {
dec_and_free(rslt5);
Value *rslt1 = arityImpl_708(empty_list, arg0);
Value *rslt2 = arityImpl_971(empty_list, rslt1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_979;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_978 = malloc_function(1);
fn_978->type = FunctionType;
fn_978->name = "anon";
fn_978->arityCount = 1;
fn_978->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_261(empty_list, rslt2, (Value *)fn_978);
incRef(rslt4);
cond0 = rslt4;
dec_and_free(rslt1);
dec_and_free((Value *)fn_978);
dec_and_free(rslt4);
dec_and_free(rslt2);
}
return(cond0);
};


// --------- repeat main body --------------
Function fn_976 = {FunctionType, -1, "repeat", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_977}}};


 int64_t sym_counter = 0;

// --------- get-sym-count --------------
Function fn_981;
Value *arityImpl_982(List *closures) {

  return numberValue(sym_counter);
};


// --------- get-sym-count main body --------------
Function fn_981 = {FunctionType, -1, "get-sym-count", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_982}}};


// --------- set-sym-count --------------
Function fn_984;
Value *arityImpl_985(List *closures, Value *arg0) {

  sym_counter = ((Number *)arg0)->numVal;
  return true;
};


// --------- set-sym-count main body --------------
Function fn_984 = {FunctionType, -1, "set-sym-count", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_985}}};


// --------- new-sym-count --------------
Function fn_987;
Value *arityImpl_988(List *closures) {

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
Function fn_987 = {FunctionType, -1, "new-sym-count", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_988}}};


// --------- gensym --------------
Function fn_990;
Value *arityImpl_991(List *closures, Value *arg0) {
Value *rslt0 = arityImpl_988(empty_list);
List *varArgs1 = empty_list;
incRef((Value *)rslt0);
varArgs1 = (List *)listCons((Value *)rslt0, varArgs1);
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_771(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_90(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt0);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- gensym main body --------------
Function fn_990 = {FunctionType, -1, "gensym", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_991}}};

Value *get(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_394((List *)0, node, key, val, hash, shift));
}
Value *assoc(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_396((List *)0, node, key, val, hash, shift));
}
Value *valsEqual(List *x, Value *v1, Value *v2) {
  return(protoFnImpl_285(x, v1, v2));
}
Value *sha1(Value *v) {
  return(protoFnImpl_429((List *)0, v));
}
Value *hashSeq(Value *n, Value *s) {
  return(protoFnImpl_398((List *)0, n, s));
}
Value *count(Value *n) {
  return(protoFnImpl_313((List *)0, n));
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
strInfo = listCons(stringValue("_str_57"), empty_list);
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
strInfo = listCons(stringValue("_str_54"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_45"), empty_list);
strInfo = listCons(stringValue("<maybe "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_55"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_44"), empty_list);
strInfo = listCons(stringValue("<nothing>"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
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
strInfo = listCons(stringValue("_str_33"), empty_list);
strInfo = listCons(stringValue(":match*-two-args"), strInfo);
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
strInfo = listCons(stringValue("_str_42"), empty_list);
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
strInfo = listCons(stringValue("_str_40"), empty_list);
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
strInfo = listCons(stringValue("_str_47"), empty_list);
strInfo = listCons(stringValue("maybe-val"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_43"), empty_list);
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
strInfo = listCons(stringValue("_str_60"), empty_list);
strInfo = listCons(stringValue("Could not look up "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_48"), empty_list);
strInfo = listCons(stringValue("<Fn: "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_23"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; int count; List *closures; int variadic; void *fn;} FnArity;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_32"), empty_list);
strInfo = listCons(stringValue(":match*-one-arg"), strInfo);
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
strInfo = listCons(stringValue("_str_61"), empty_list);
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
strInfo = listCons(stringValue("_str_59"), empty_list);
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
strInfo = listCons(stringValue("_str_58"), empty_list);
strInfo = listCons(stringValue("{"), strInfo);
strs = listCons((Value *)strInfo, strs);
return((Value *)strs);
}

Value *keyword_literals() {
List *kws = empty_list;
List *kwInfo;
kwInfo = listCons(stringValue("_kw_1"), empty_list);
kwInfo = listCons(keywordValue(":k"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_2"), empty_list);
kwInfo = listCons(keywordValue(":get-in-not-found"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_0"), empty_list);
kwInfo = listCons(keywordValue(":m"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_3"), empty_list);
kwInfo = listCons(keywordValue(":update-in-nil"), kwInfo);
kws = listCons((Value *)kwInfo, kws);
kwInfo = listCons(stringValue("_kw_4"), empty_list);
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
impl = listCons(stringValue("(Value *)&protoFn_528"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".v"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_493;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_492"), protoInfo);
protoInfo = listCons(stringValue("Getter/.v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_508"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_451"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_210"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flatten"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_209;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_208"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flatten"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_643"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_716"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_744"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_294;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_293"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_651"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_518"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_603"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_845"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_813"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_877"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_720"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_748"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_461"), impl);
impl = listCons(numberValue(13), impl);
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
impl = listCons(stringValue("(Value *)&fn_652"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_911"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_934"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_721"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_944"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_749"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_615"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_463"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_283"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("=*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_282;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_281"), protoInfo);
protoInfo = listCons(stringValue("core/Eq/=*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("bippity"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_183;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_182"), protoInfo);
protoInfo = listCons(stringValue("core/Variant/bippity"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_647"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("crush"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_361;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_360"), protoInfo);
protoInfo = listCons(stringValue("core/Crushable/crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_646"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_719"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_747"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("reduce"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_309;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_308"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/reduce"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_277"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("serialize"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_276;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_275"), protoInfo);
protoInfo = listCons(stringValue("core/Serializable/serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_641"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("traverse"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_356;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_355"), protoInfo);
protoInfo = listCons(stringValue("core/Traversable/traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_848"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_816"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_880"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("vals"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_407;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_406"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_658"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_522"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_467"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_257"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_256;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_255"), protoInfo);
protoInfo = listCons(stringValue("core/Functor/map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_933"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_714"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_943"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_742"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_613"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("sha1"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_427;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_426"), protoInfo);
protoInfo = listCons(stringValue("core/Hash/sha1"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_937"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_948"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_265"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_264;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_263"), protoInfo);
protoInfo = listCons(stringValue("core/Named/name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_224"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("duplicate"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_223;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_222"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/duplicate"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_852"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_820"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_884"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("hash-seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_392;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_391"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/hash-seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_514"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_601"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_499"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_457"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_241"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("apply*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_240;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_239"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_648"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_510"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_453"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_207"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("flat-map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_206;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_205"), protoInfo);
protoInfo = listCons(stringValue("core/Monad/flat-map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_656"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_724"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_752"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_333;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_332"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_645"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_842"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_810"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_874"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_717"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_745"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("count"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_297;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_296"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/count"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_846"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_814"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_878"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_411"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_410;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_409"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_854"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_822"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_886"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_386;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_385"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/get*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_853"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_821"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_885"), impl);
impl = listCons(numberValue(12), impl);
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
impl = listCons(stringValue("(Value *)&fn_37"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_526"), impl);
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
protoInfo = listCons(symbolValue("type-name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_4;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_3"), protoInfo);
protoInfo = listCons(stringValue("Getter/type-name"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_847"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_815"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_879"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("keys"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_413;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_412"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_936"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_501"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_947"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_557"), impl);
impl = listCons(numberValue(16), impl);
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
impl = listCons(stringValue("(Value *)&fn_649"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_512"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_455"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_238"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("wrap"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_237;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_236"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/wrap"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_187"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("match*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_186;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_185"), protoInfo);
protoInfo = listCons(stringValue("core/Variant/match*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_503"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_559"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_201"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("instance?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_200;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_199"), protoInfo);
protoInfo = listCons(stringValue("core/Type/instance?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_642"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_843"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_811"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_875"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_715"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_743"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("empty?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_306;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_305"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/empty?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extend"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_220;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_219"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extend"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_524"), impl);
impl = listCons(numberValue(15), impl);
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
impl = listCons(stringValue("(Value *)&fn_654"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_851"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_819"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_883"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_723"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_751"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_330;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_329"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_614"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_289"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("<*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_288;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_287"), protoInfo);
protoInfo = listCons(stringValue("core/Ord/<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_655"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("m-first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_336;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_335"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/m-first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("destruct"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_303;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_302"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/destruct"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("dissoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_404;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_403"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/dissoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_653"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_340"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_339;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_338"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq?"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
protoInfo = listCons(symbolValue("extract"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_226;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_225"), protoInfo);
protoInfo = listCons(stringValue("core/Comonad/extract"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_644"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_718"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_746"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("conj"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_300;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_299"), protoInfo);
protoInfo = listCons(stringValue("core/Collection/conj"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_657"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_725"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_753"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("rest"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_327;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_326"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_849"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_817"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_881"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_401;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_400"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_650"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_516"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_602"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_844"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_812"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_876"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_555"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_459"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("zero"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_369;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_368"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_684"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_520"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_604"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_850"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_935"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_818"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_882"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_722"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_945"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_750"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_616"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_465"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_271"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("string-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_270;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_269"), protoInfo);
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
arityInfo = listCons(stringValue("arityImpl_687"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_686"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_762"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_761"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(5), empty_list);
arityInfo = listCons(stringValue("arityImpl_959"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_958"), fnInfo);
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
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("protoImpl_549"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_526"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_952"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_946"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_313"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_297"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_760"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_748"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_835"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_818"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_285"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_282"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_443"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_441"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_442"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_440"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_634"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_633"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_670"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_650"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_486"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_467"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_671"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_651"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_778"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_777"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_903"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_884"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("protoImpl_562"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_555"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_618"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_614"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_690"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_689"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_540"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_519"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_895"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_878"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_871"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_852"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_887"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_874"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_664"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_646"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_429"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_427"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_697"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_53"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_665"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_647"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_565"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_560"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_358"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_356"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_758"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_746"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_533"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_510"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_675"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_655"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_928"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_927"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoImpl_564"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_557"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_767"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_751"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_321"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_309"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_888"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_875"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_890"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_877"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_909"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_623"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_624"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_622"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_341"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_327"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_599"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_598"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_579"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_578"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_577"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_661"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_643"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_807"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_806"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_537"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_514"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_732"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_720"), fnInfo);
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
arityInfo = listCons(stringValue("protoImpl_472"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_453"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_156"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_155"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_726"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_714"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_566"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_559"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_373"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_369"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_678"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_658"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_940"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_935"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_965"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_964"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_824"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_811"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_197"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_196"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_545"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_522"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_755"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_743"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_781"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_780"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_801"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_800"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_799"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_962"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_961"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_319"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_306"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_547"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_524"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_324"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_323"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_628"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_626"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_739"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_723"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_907"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_422"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_410"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_394"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_386"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_483"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_466"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_291"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_288"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_553"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_503"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("protoImpl_539"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_516"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_478"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_459"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_212"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_206"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_730"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_718"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_279"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_276"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_591"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_590"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_435"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_434"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_697"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_696"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_228"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_220"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_112"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_111"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_856"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_843"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_685"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_684"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_841"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_822"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_913"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_912"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_446"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_445"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_317"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_303"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_548"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_527"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_950"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_944"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_617"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_613"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_754"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_742"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_543"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_520"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_673"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_653"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_826"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_813"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_825"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_812"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_396"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_389"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_481"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_464"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(7), empty_list);
arityInfo = listCons(stringValue("arityImpl_991"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_990"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_840"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_821"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_896"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_879"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_784"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_785"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_783"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_941"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_936"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_231"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_223"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_353"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_352"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_834"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_817"), fnInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_350"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_339"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_473"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_456"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_680"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_679"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_479"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_462"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_677"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_657"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_804"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_803"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_475"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_458"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_968"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_967"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_954"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_948"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_727"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_715"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_619"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_615"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_942"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_937"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_250"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_240"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_985"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_858"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_845"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_605"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_601"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_663"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_645"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_676"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_656"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_477"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_460"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_672"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_652"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_343"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_330"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_662"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_644"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_498"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_450"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_563"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_558"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_833"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_816"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_901"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_900"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_705"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_704"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_551"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_528"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_668"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_648"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_867"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_850"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_596"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_595"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_904"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_885"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_611"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_610"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_731"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_719"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_506"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_499"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_864"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_847"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_866"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_849"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_432"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_431"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_538"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_517"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_953"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_947"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_637"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_636"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_552"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_504"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_870"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_851"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_857"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_844"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_127"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_126"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_623"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_624"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_235"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_585"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_584"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_837"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_836"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_931"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_930"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_606"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_602"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_823"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_810"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_505"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_500"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_712"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_711"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_710"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_768"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_752"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_956"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_955"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_474"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_455"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_791"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_790"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_620"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_616"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_471"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_454"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_607"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_603"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_498"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_501"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_974"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_973"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_476"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_457"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_832"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_815"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_769"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_753"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_794"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_793"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_897"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_880"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_741"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_725"), fnInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_347"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_336"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_575"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_574"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_398"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_392"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_788"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_787"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_728"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_716"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_898"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_881"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_588"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_587"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoImpl_535"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_512"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_531"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_508"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_253"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_252"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_419"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_407"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_261"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_256"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_759"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_747"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_674"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_654"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_939"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_934"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_376"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_375"), fnInfo);
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
arityInfo = listCons(stringValue("protoImpl_541"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_518"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_417"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_404"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_192"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_194"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_186"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_738"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_722"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_914"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_911"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_765"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_749"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_988"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_987"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_311"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_294"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_345"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_333"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_485"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_468"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_865"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_848"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_380"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_379"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_378"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_756"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_744"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_938"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_933"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_216"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_215"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_894"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_893"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_217"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_209"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_766"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_750"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_118"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_117"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_729"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_717"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_495"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_493"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_639"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_638"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_371"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_366"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_383"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_382"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_363"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_361"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_180"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_925"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_924"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_899"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_882"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_831"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_814"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_243"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_237"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_892"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_891"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_971"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_970"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_872"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_853"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_534"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_513"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_951"), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_873"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_854"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_470"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_451"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_918"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_917"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_273"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_270"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_757"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_745"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_561"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_556"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_484"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_465"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_507"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_502"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_542"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_521"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_669"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_649"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_773"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_772"), fnInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_839"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_820"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_438"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_437"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_203"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_200"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_902"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_883"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_737"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_721"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_490"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_489"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_188"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_183"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_949"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_943"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_699"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_698"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_797"), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_740"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_724"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_708"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_707"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_693"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_692"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_862"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_861"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_536"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_515"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_267"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_264"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_855"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_842"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_982"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_981"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_612"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_604"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_889"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_876"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_860"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_859"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_830"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_829"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("protoImpl_482"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_463"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_659"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_641"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_905"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_886"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_315"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_300"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_469"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_452"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_838"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_819"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_702"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_701"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_734"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_733"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_572"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_570"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_571"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_569"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_424"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_413"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_415"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_401"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_582"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_581"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_233"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_226"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_480"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_461"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_660"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_642"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_863"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_846"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_771"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_770"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_869"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_868"), fnInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_327"), symInfo);
symInfo = listCons(stringValue("Function protoFn_327"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_885"), symInfo);
symInfo = listCons(stringValue("Function fn_885"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(16), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_567"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_567"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_330"), symInfo);
symInfo = listCons(stringValue("Function protoFn_330"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_237"), symInfo);
symInfo = listCons(stringValue("Function protoFn_237"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_689"), symInfo);
symInfo = listCons(stringValue("Function fn_689"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_352"), symInfo);
symInfo = listCons(stringValue("Function fn_352"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_883"), symInfo);
symInfo = listCons(stringValue("Function fn_883"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_686"), symInfo);
symInfo = listCons(stringValue("Function fn_686"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("prn"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_440"), symInfo);
symInfo = listCons(stringValue("Function fn_440"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_917"), symInfo);
symInfo = listCons(stringValue("Function fn_917"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_636"), symInfo);
symInfo = listCons(stringValue("Function fn_636"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_577"), symInfo);
symInfo = listCons(stringValue("Function fn_577"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_614"), symInfo);
symInfo = listCons(stringValue("Function fn_614"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_927"), symInfo);
symInfo = listCons(stringValue("Function fn_927"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_386"), symInfo);
symInfo = listCons(stringValue("Function protoFn_386"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_196"), symInfo);
symInfo = listCons(stringValue("Function fn_196"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("alert"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_11"), symInfo);
symInfo = listCons(stringValue("Number _num_11"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("ArrayNode"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_401"), symInfo);
symInfo = listCons(stringValue("Function protoFn_401"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_924"), symInfo);
symInfo = listCons(stringValue("Function fn_924"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_206"), symInfo);
symInfo = listCons(stringValue("Function protoFn_206"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_698"), symInfo);
symInfo = listCons(stringValue("Function fn_698"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("inc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_220"), symInfo);
symInfo = listCons(stringValue("Function protoFn_220"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extend"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_648"), symInfo);
symInfo = listCons(stringValue("Function fn_648"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_981"), symInfo);
symInfo = listCons(stringValue("Function fn_981"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-sym-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_633"), symInfo);
symInfo = listCons(stringValue("Function fn_633"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_366"), symInfo);
symInfo = listCons(stringValue("Function protoFn_366"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_707"), symInfo);
symInfo = listCons(stringValue("Function fn_707"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_389"), symInfo);
symInfo = listCons(stringValue("Function protoFn_389"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_809"), symInfo);
symInfo = listCons(stringValue("Value *var_809;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("emptyBMI"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_655"), symInfo);
symInfo = listCons(stringValue("Function fn_655"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m-first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_333"), symInfo);
symInfo = listCons(stringValue("Function protoFn_333"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_906"), symInfo);
symInfo = listCons(stringValue("Function fn_906"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(14), empty_list);
symInfo = listCons(stringValue("var_450"), symInfo);
symInfo = listCons(stringValue("Value *var_450"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe-val"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_783"), symInfo);
symInfo = listCons(stringValue("Function fn_783"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_264"), symInfo);
symInfo = listCons(stringValue("Function protoFn_264"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_753"), symInfo);
symInfo = listCons(stringValue("Function fn_753"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_369"), symInfo);
symInfo = listCons(stringValue("Function protoFn_369"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_282"), symInfo);
symInfo = listCons(stringValue("Function protoFn_282"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_881"), symInfo);
symInfo = listCons(stringValue("Function fn_881"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_294"), symInfo);
symInfo = listCons(stringValue("Function protoFn_294"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_529"), symInfo);
symInfo = listCons(stringValue("Function fn_529"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_943"), symInfo);
symInfo = listCons(stringValue("Function fn_943"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_252"), symInfo);
symInfo = listCons(stringValue("Function fn_252"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_437"), symInfo);
symInfo = listCons(stringValue("Function fn_437"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_297"), symInfo);
symInfo = listCons(stringValue("Function protoFn_297"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_984"), symInfo);
symInfo = listCons(stringValue("Function fn_984"), symInfo);
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
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_19"), symInfo);
symInfo = listCons(stringValue("String _str_19"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("NumberVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(17), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_915"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_915"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-found"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_679"), symInfo);
symInfo = listCons(stringValue("Function fn_679"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_990"), symInfo);
symInfo = listCons(stringValue("Function fn_990"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("gensym"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_944"), symInfo);
symInfo = listCons(stringValue("Function fn_944"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_876"), symInfo);
symInfo = listCons(stringValue("Function fn_876"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_622"), symInfo);
symInfo = listCons(stringValue("Function fn_622"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_200"), symInfo);
symInfo = listCons(stringValue("Function protoFn_200"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_587"), symInfo);
symInfo = listCons(stringValue("Function fn_587"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_658"), symInfo);
symInfo = listCons(stringValue("Function fn_658"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_270"), symInfo);
symInfo = listCons(stringValue("Function protoFn_270"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_569"), symInfo);
symInfo = listCons(stringValue("Function fn_569"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m="), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(1), empty_list);
symInfo = listCons(stringValue("(Value *)&_str_23"), symInfo);
symInfo = listCons(stringValue("String _str_23"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("FnArityVal"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_961"), symInfo);
symInfo = listCons(stringValue("Function fn_961"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keyword?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_76"), symInfo);
symInfo = listCons(stringValue("Value *var_76;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("false"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_240"), symInfo);
symInfo = listCons(stringValue("Function protoFn_240"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_300"), symInfo);
symInfo = listCons(stringValue("Function protoFn_300"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_303"), symInfo);
symInfo = listCons(stringValue("Function protoFn_303"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("destruct"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_880"), symInfo);
symInfo = listCons(stringValue("Function fn_880"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_601"), symInfo);
symInfo = listCons(stringValue("Function fn_601"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_976"), symInfo);
symInfo = listCons(stringValue("Function fn_976"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("repeat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_276"), symInfo);
symInfo = listCons(stringValue("Function protoFn_276"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_964"), symInfo);
symInfo = listCons(stringValue("Function fn_964"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("number?"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_404"), symInfo);
symInfo = listCons(stringValue("Function protoFn_404"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dissoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_886"), symInfo);
symInfo = listCons(stringValue("Function fn_886"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_256"), symInfo);
symInfo = listCons(stringValue("Function protoFn_256"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_584"), symInfo);
symInfo = listCons(stringValue("Function fn_584"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_223"), symInfo);
symInfo = listCons(stringValue("Function protoFn_223"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_930"), symInfo);
symInfo = listCons(stringValue("Function fn_930"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_692"), symInfo);
symInfo = listCons(stringValue("Function fn_692"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_973"), symInfo);
symInfo = listCons(stringValue("Function fn_973"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_336"), symInfo);
symInfo = listCons(stringValue("Function protoFn_336"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_509"), symInfo);
symInfo = listCons(stringValue("Function fn_509"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_445"), symInfo);
symInfo = listCons(stringValue("Function fn_445"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_323"), symInfo);
symInfo = listCons(stringValue("Function fn_323"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_392"), symInfo);
symInfo = listCons(stringValue("Function protoFn_392"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_752"), symInfo);
symInfo = listCons(stringValue("Function fn_752"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_746"), symInfo);
symInfo = listCons(stringValue("Function fn_746"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_696"), symInfo);
symInfo = listCons(stringValue("Function fn_696"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_431"), symInfo);
symInfo = listCons(stringValue("Function fn_431"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_306"), symInfo);
symInfo = listCons(stringValue("Function protoFn_306"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_793"), symInfo);
symInfo = listCons(stringValue("Function fn_793"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_874"), symInfo);
symInfo = listCons(stringValue("Function fn_874"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_382"), symInfo);
symInfo = listCons(stringValue("Function fn_382"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_877"), symInfo);
symInfo = listCons(stringValue("Function fn_877"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_879"), symInfo);
symInfo = listCons(stringValue("Function fn_879"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_560"), symInfo);
symInfo = listCons(stringValue("Function fn_560"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_598"), symInfo);
symInfo = listCons(stringValue("Function fn_598"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_978"), symInfo);
symInfo = listCons(stringValue("Function fn_978"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_799"), symInfo);
symInfo = listCons(stringValue("Function fn_799"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_574"), symInfo);
symInfo = listCons(stringValue("Function fn_574"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_434"), symInfo);
symInfo = listCons(stringValue("Function fn_434"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_378"), symInfo);
symInfo = listCons(stringValue("Function fn_378"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_803"), symInfo);
symInfo = listCons(stringValue("Function fn_803"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("last"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_226"), symInfo);
symInfo = listCons(stringValue("Function protoFn_226"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("extract"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_967"), symInfo);
symInfo = listCons(stringValue("Function fn_967"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_710"), symInfo);
symInfo = listCons(stringValue("Function fn_710"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_288"), symInfo);
symInfo = listCons(stringValue("Function protoFn_288"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(13), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_487"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_487"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_361"), symInfo);
symInfo = listCons(stringValue("Function protoFn_361"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_356"), symInfo);
symInfo = listCons(stringValue("Function protoFn_356"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_489"), symInfo);
symInfo = listCons(stringValue("Function fn_489"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("any?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_527"), symInfo);
symInfo = listCons(stringValue("Function fn_527"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_704"), symInfo);
symInfo = listCons(stringValue("Function fn_704"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_947"), symInfo);
symInfo = listCons(stringValue("Function fn_947"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_407"), symInfo);
symInfo = listCons(stringValue("Function protoFn_407"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_701"), symInfo);
symInfo = listCons(stringValue("Function fn_701"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_958"), symInfo);
symInfo = listCons(stringValue("Function fn_958"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_590"), symInfo);
symInfo = listCons(stringValue("Function fn_590"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_747"), symInfo);
symInfo = listCons(stringValue("Function fn_747"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_183"), symInfo);
symInfo = listCons(stringValue("Function protoFn_183"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("bippity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_427"), symInfo);
symInfo = listCons(stringValue("Function protoFn_427"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("sha1"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_806"), symInfo);
symInfo = listCons(stringValue("Function fn_806"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_878"), symInfo);
symInfo = listCons(stringValue("Function fn_878"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_955"), symInfo);
symInfo = listCons(stringValue("Function fn_955"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("symbol?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(2), empty_list);
symInfo = listCons(stringValue("(Value *)&_num_3"), symInfo);
symInfo = listCons(stringValue("Number _num_3"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("Function"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_179"), symInfo);
symInfo = listCons(stringValue("Function fn_179"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_770"), symInfo);
symInfo = listCons(stringValue("Function fn_770"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_641"), symInfo);
symInfo = listCons(stringValue("Function fn_641"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("traverse_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_309"), symInfo);
symInfo = listCons(stringValue("Function protoFn_309"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_653"), symInfo);
symInfo = listCons(stringValue("Function fn_653"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_777"), symInfo);
symInfo = listCons(stringValue("Function fn_777"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_987"), symInfo);
symInfo = listCons(stringValue("Function fn_987"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_209"), symInfo);
symInfo = listCons(stringValue("Function protoFn_209"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flatten"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_595"), symInfo);
symInfo = listCons(stringValue("Function fn_595"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_410"), symInfo);
symInfo = listCons(stringValue("Function protoFn_410"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_744"), symInfo);
symInfo = listCons(stringValue("Function fn_744"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_970"), symInfo);
symInfo = listCons(stringValue("Function fn_970"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_375"), symInfo);
symInfo = listCons(stringValue("Function fn_375"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_790"), symInfo);
symInfo = listCons(stringValue("Function fn_790"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_875"), symInfo);
symInfo = listCons(stringValue("Function fn_875"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_525"), symInfo);
symInfo = listCons(stringValue("Function fn_525"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-args_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_780"), symInfo);
symInfo = listCons(stringValue("Function fn_780"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("drop"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_186"), symInfo);
symInfo = listCons(stringValue("Function protoFn_186"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("match*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_945"), symInfo);
symInfo = listCons(stringValue("Function fn_945"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_884"), symInfo);
symInfo = listCons(stringValue("Function fn_884"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_787"), symInfo);
symInfo = listCons(stringValue("Function fn_787"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("replace-at-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_796"), symInfo);
symInfo = listCons(stringValue("Function fn_796"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_649"), symInfo);
symInfo = listCons(stringValue("Function fn_649"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_581"), symInfo);
symInfo = listCons(stringValue("Function fn_581"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_948"), symInfo);
symInfo = listCons(stringValue("Function fn_948"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_413"), symInfo);
symInfo = listCons(stringValue("Function protoFn_413"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_339"), symInfo);
symInfo = listCons(stringValue("Function protoFn_339"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_493"), symInfo);
symInfo = listCons(stringValue("Function protoFn_493"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_647"), symInfo);
symInfo = listCons(stringValue("Function fn_647"), symInfo);
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
cnts = listCons(numberValue(993), cnts);
return((Value *)cnts);
}

