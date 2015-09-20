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
Value *rslt1 = arityImpl_180(empty_list, (Value *)&_str_32);
return(rslt1);
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
Value *cond2;

if (isTrue(arg0)) {
dec_and_free(arg0);
incRef(var_75);
cond2 = var_75;
} else {
dec_and_free(arg0);
Value *rslt6;
if((var_53)->type != FunctionType) {
rslt6 = protoFnImpl_11(empty_list, var_53, arg1);
} else {
FnArity *arity3 = findFnArity(var_53, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
Value *rslt7 = arityImpl_96(empty_list);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
}
return(cond2);
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
Value *rslt3 = arityImpl_180(empty_list, (Value *)&_str_34);
Value *rslt4 = arityImpl_96(empty_list);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
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
Value *rslt2 = protoFnImpl_212(empty_list, arg0, (Value *)&fn_215);
return(rslt2);
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

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[22];} _str_37 = {1, -1, 21,"'<*' not implemented:"};
ProtoImpls *protoImpls_235;
Function protoFn_236;
Value *arityImpl_238(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_37, arg0);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_37, arg0);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(arg0);
varArgs3 = (List *)listCons(arg0, varArgs3);
incRef((Value *)&_str_37);
varArgs3 = (List *)listCons((Value *)&_str_37, varArgs3);
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

Value *protoFnImpl_239(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_235);
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
FnArity protoFnArity_240 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_239};
Function defaultFn_237 = {FunctionType, -1, "<*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_238}}};

Function protoFn_236 = {FunctionType, -1, "<*", 1, {&protoFnArity_240}};

// forward declaration for 'comprehend'
Value *var_241;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[27];} _str_38 = {1, -1, 26,"*** 'wrap' not implemented"};
ProtoImpls *protoImpls_242;
Function protoFn_243;
Value *arityImpl_248(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, var_53, (Value *)&_str_38);
} else {
FnArity *arity2 = findFnArity(var_53, 1);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_38);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef((Value *)&_str_38);
varArgs3 = (List *)listCons((Value *)&_str_38, varArgs3);
rslt5 = fn4(arity2->closures, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_53)->name);
  abort();
}
}
return(rslt5);
};

Value *protoFnImpl_249(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_242);
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
FnArity protoFnArity_250 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_249};
Function defaultFn_244 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_248}}};

Function protoFn_243 = {FunctionType, -1, "wrap", 1, {&protoFnArity_250}};

ProtoImpls *protoImpls_245;
Function protoFn_246;

// --------- anon --------------
Function fn_252;
Value *arityImpl_253(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt5;
if((var_241)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_241, arg0, val1);
} else {
FnArity *arity2 = findFnArity(var_241, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_241)->name);
  abort();
}
}
return(rslt5);
};


// --------- anon --------------
Function fn_254;
Value *arityImpl_255(List *closures, Value *arg0) {
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
Value *rslt6 = protoFnImpl_249(empty_list, val1, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};

Value *arityImpl_251(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt5 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_255;
incRef((Value *)arg0);
arity_6->closures = listCons((Value *)arg0, (List *)arity_6->closures);
Function *fn_254 = malloc_function(1);
fn_254->type = FunctionType;
fn_254->name = "anon";
fn_254->arityCount = 1;
fn_254->arities[0] = arity_6;
Value *rslt7 = protoFnImpl_212(empty_list, arg0, (Value *)fn_254);
incRef(rslt7);
cond2 = rslt7;
dec_and_free((Value *)fn_254);
dec_and_free(rslt7);
} else {
dec_and_free(rslt5);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 1;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_253;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_252 = malloc_function(1);
fn_252->type = FunctionType;
fn_252->name = "anon";
fn_252->arityCount = 1;
fn_252->arities[0] = arity_3;
Value *rslt4 = protoFnImpl_212(empty_list, arg0, (Value *)fn_252);
incRef(rslt4);
cond2 = rslt4;
dec_and_free((Value *)fn_252);
dec_and_free(rslt4);
}
return(cond2);
};

Value *protoFnImpl_256(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_245);
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
FnArity protoFnArity_257 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_256};
Function defaultFn_247 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_251}}};

Function protoFn_246 = {FunctionType, -1, "apply*", 1, {&protoFnArity_257}};


// --------- list --------------
Function fn_258;
Value *arityImpl_259(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
incRef(arg0);
return(arg0);
};

// --------- list main body --------------
Function fn_258 = {FunctionType, -1, "list", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_259}}};

ProtoImpls *protoImpls_261;
Function protoFn_262;

// --------- anon --------------
Function fn_265;
Value *arityImpl_266(List *closures, Value *arg0) {
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
Value *rslt7 = protoFnImpl_249(empty_list, val1, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt7);
return(rslt7);
};

Value *arityImpl_264(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_266;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
Function *fn_265 = malloc_function(1);
fn_265->type = FunctionType;
fn_265->name = "anon";
fn_265->arityCount = 1;
fn_265->arities[0] = arity_2;
Value *rslt3 = protoFnImpl_212(empty_list, arg0, (Value *)fn_265);
incRef(rslt3);
dec_and_free((Value *)fn_265);
dec_and_free(rslt3);
return(rslt3);
};

Value *protoFnImpl_267(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_261);
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
FnArity protoFnArity_268 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_267};
Function defaultFn_263 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_264}}};

Function protoFn_262 = {FunctionType, -1, "map", 1, {&protoFnArity_268}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[33];} _str_39 = {1, -1, 32,"'name' not implemented for type "};
ProtoImpls *protoImpls_269;
Function protoFn_270;
Value *arityImpl_272(List *closures, Value *arg0) {
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

Value *protoFnImpl_273(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_269);
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
FnArity protoFnArity_274 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_273};
Function defaultFn_271 = {FunctionType, -1, "name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_272}}};

Function protoFn_270 = {FunctionType, -1, "name", 1, {&protoFnArity_274}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[39];} _str_40 = {1, -1, 38,"'string-list' not implemented for type"};
ProtoImpls *protoImpls_275;
Function protoFn_276;
Value *arityImpl_278(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_25(empty_list, arg0);
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_40, rslt1);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_40, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
incRef((Value *)&_str_40);
varArgs3 = (List *)listCons((Value *)&_str_40, varArgs3);
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

Value *protoFnImpl_279(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_275);
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
FnArity protoFnArity_280 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_279};
Function defaultFn_277 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_278}}};

Function protoFn_276 = {FunctionType, -1, "string-list", 1, {&protoFnArity_280}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[37];} _str_41 = {1, -1, 36,"'serialize' not implemented for type"};
ProtoImpls *protoImpls_281;
Function protoFn_282;
Value *arityImpl_284(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_25(empty_list, arg0);
Value *rslt5;
if((var_53)->type != FunctionType) {
rslt5 = protoFnImpl_13(empty_list, var_53, (Value *)&_str_41, rslt1);
} else {
FnArity *arity2 = findFnArity(var_53, 2);
if(arity2 != (FnArity *)0 && !arity2->variadic) {
FnType2 *fn4 = (FnType2 *)arity2->fn;
rslt5 = fn4(arity2->closures, (Value *)&_str_41, rslt1);
} else if(arity2 != (FnArity *)0 && arity2->variadic) {
FnType1 *fn4 = (FnType1 *)arity2->fn;
List *varArgs3 = empty_list;
incRef(rslt1);
varArgs3 = (List *)listCons(rslt1, varArgs3);
incRef((Value *)&_str_41);
varArgs3 = (List *)listCons((Value *)&_str_41, varArgs3);
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

Value *protoFnImpl_285(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_281);
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
FnArity protoFnArity_286 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_285};
Function defaultFn_283 = {FunctionType, -1, "serialize", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_284}}};

Function protoFn_282 = {FunctionType, -1, "serialize", 1, {&protoFnArity_286}};

Number _num_13 = {2, -1, 0};
ProtoImpls *protoImpls_287;
Function protoFn_288;
Value *arityImpl_290(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt3 = arityImpl_102(empty_list, arg0, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
Value *rslt4 = protoFnImpl_27(empty_list, arg0);
Value *rslt5 = protoFnImpl_27(empty_list, arg1);
Value *rslt9;
FnArity *arity6 = findFnArity((Value *)&protoFn_288, 2);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&protoFn_288)->name);
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

Value *protoFnImpl_291(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_287);
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
FnArity protoFnArity_292 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_291};
Function defaultFn_289 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_290}}};

Function protoFn_288 = {FunctionType, -1, "=*", 1, {&protoFnArity_292}};

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

ProtoImpls *protoImpls_323;
Function protoFn_324;
Value *protoFnImpl_338(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_323);
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
FnArity protoFnArity_339 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_338};
Function protoFn_324 = {FunctionType, -1, "rest", 1, {&protoFnArity_339}};

ProtoImpls *protoImpls_326;
Function protoFn_327;
Value *protoFnImpl_340(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_326);
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
FnArity protoFnArity_341 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_340};
Function protoFn_327 = {FunctionType, -1, "seq", 1, {&protoFnArity_341}};

ProtoImpls *protoImpls_329;
Function protoFn_330;
Value *protoFnImpl_342(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_329);
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
FnArity protoFnArity_343 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_342};
Function protoFn_330 = {FunctionType, -1, "first", 1, {&protoFnArity_343}};

ProtoImpls *protoImpls_332;
Function protoFn_333;
Value *protoFnImpl_344(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_332);
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
FnArity protoFnArity_345 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_344};
Function protoFn_333 = {FunctionType, -1, "m-first", 1, {&protoFnArity_345}};

ProtoImpls *protoImpls_335;
Function protoFn_336;
Value *arityImpl_346(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};

Value *protoFnImpl_347(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_335);
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
FnArity protoFnArity_348 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_347};
Function defaultFn_337 = {FunctionType, -1, "seq?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_346}}};

Function protoFn_336 = {FunctionType, -1, "seq?", 1, {&protoFnArity_348}};


// --------- second --------------
Function fn_349;
Value *arityImpl_350(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_338(empty_list, arg0);
Value *rslt2 = protoFnImpl_342(empty_list, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- second main body --------------
Function fn_349 = {FunctionType, -1, "second", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_350}}};

ProtoImpls *protoImpls_352;
Function protoFn_353;
Value *protoFnImpl_355(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_352);
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
FnArity protoFnArity_356 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_355};
Function protoFn_353 = {FunctionType, -1, "traverse", 1, {&protoFnArity_356}};

ProtoImpls *protoImpls_357;
Function protoFn_358;
Value *protoFnImpl_360(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_357);
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
FnArity protoFnArity_361 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_360};
Function protoFn_358 = {FunctionType, -1, "crush", 1, {&protoFnArity_361}};

ProtoImpls *protoImpls_362;
Function protoFn_363;
Value *protoFnImpl_368(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_362);
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
FnArity protoFnArity_369 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_368};
Function protoFn_363 = {FunctionType, -1, "comp*", 1, {&protoFnArity_369}};

ProtoImpls *protoImpls_365;
Function protoFn_366;
Value *protoFnImpl_370(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_365);
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
FnArity protoFnArity_371 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_370};
Function protoFn_366 = {FunctionType, -1, "zero", 1, {&protoFnArity_371}};


// --------- apply --------------
Function fn_372;
Value *arityImpl_373(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = protoFnImpl_256(empty_list, arg0, arg1);
return(rslt2);
};

// --------- apply main body --------------
Function fn_372 = {FunctionType, -1, "apply", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_373}}};


// --------- apply-to --------------
Function fn_375;
Value *arityImpl_376(List *closures, Value *arg0) {
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

Value *arityImpl_377(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = arityImpl_141(empty_list, arg1);
Value *rslt3 = protoFnImpl_249(empty_list, rslt2, arg0);
Value *rslt4 = protoFnImpl_256(empty_list, rslt3, arg1);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- apply-to main body --------------
Function fn_375 = {FunctionType, -1, "apply-to", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_376}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_377}}};


// --------- comp --------------
Function fn_379;
Value *arityImpl_380(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_381(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = protoFnImpl_368(empty_list, arg0, arg1);
return(rslt2);
};

// --------- comp main body --------------
Function fn_379 = {FunctionType, -1, "comp", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_380}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_381}}};

ProtoImpls *protoImpls_383;
Function protoFn_384;
Value *protoFnImpl_392(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_383);
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
FnArity protoFnArity_393 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_392};
Function protoFn_384 = {FunctionType, -1, "get*", 1, {&protoFnArity_393}};

ProtoImpls *protoImpls_386;
Function protoFn_387;
Value *protoFnImpl_394(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_386);
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
FnArity protoFnArity_395 = {FnArityType, -1, 5, (List *)0, 0, protoFnImpl_394};
Function protoFn_387 = {FunctionType, -1, "assoc*", 1, {&protoFnArity_395}};

ProtoImpls *protoImpls_389;
Function protoFn_390;
Value *protoFnImpl_396(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_389);
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
FnArity protoFnArity_397 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_396};
Function protoFn_390 = {FunctionType, -1, "hash-seq", 1, {&protoFnArity_397}};

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
ProtoImpls *protoImpls_398;
Function protoFn_399;
Value *protoFnImpl_413(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_398);
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
FnArity protoFnArity_414 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_413};
Function protoFn_399 = {FunctionType, -1, "assoc", 1, {&protoFnArity_414}};

ProtoImpls *protoImpls_401;
Function protoFn_402;
Value *protoFnImpl_415(List *closures, Value *arg0, Value *arg1) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_401);
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
FnArity protoFnArity_416 = {FnArityType, -1, 2, (List *)0, 0, protoFnImpl_415};
Function protoFn_402 = {FunctionType, -1, "dissoc", 1, {&protoFnArity_416}};

ProtoImpls *protoImpls_404;
Function protoFn_405;
Value *protoFnImpl_417(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_404);
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
FnArity protoFnArity_418 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_417};
Function protoFn_405 = {FunctionType, -1, "vals", 1, {&protoFnArity_418}};

ProtoImpls *protoImpls_407;
Function protoFn_408;
Value *arityImpl_419(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_25(empty_list, arg0);
Value *rslt7;
if((var_53)->type != FunctionType) {
rslt7 = protoFnImpl_23(empty_list, var_53, (Value *)&_str_42, rslt3, (Value *)&_str_43, (Value *)&_kw_0, arg0, (Value *)&_kw_1, arg1);
} else {
FnArity *arity4 = findFnArity(var_53, 7);
if(arity4 != (FnArity *)0 && !arity4->variadic) {
FnType7 *fn6 = (FnType7 *)arity4->fn;
rslt7 = fn6(arity4->closures, (Value *)&_str_42, rslt3, (Value *)&_str_43, (Value *)&_kw_0, arg0, (Value *)&_kw_1, arg1);
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
incRef((Value *)&_str_43);
varArgs5 = (List *)listCons((Value *)&_str_43, varArgs5);
incRef(rslt3);
varArgs5 = (List *)listCons(rslt3, varArgs5);
incRef((Value *)&_str_42);
varArgs5 = (List *)listCons((Value *)&_str_42, varArgs5);
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

Value *protoFnImpl_420(List *closures, Value *arg0, Value *arg1, Value *arg2) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_407);
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
FnArity protoFnArity_421 = {FnArityType, -1, 3, (List *)0, 0, protoFnImpl_420};
Function defaultFn_409 = {FunctionType, -1, "get", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_419}}};

Function protoFn_408 = {FunctionType, -1, "get", 1, {&protoFnArity_421}};

ProtoImpls *protoImpls_410;
Function protoFn_411;
Value *protoFnImpl_422(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_410);
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
FnArity protoFnArity_423 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_422};
Function protoFn_411 = {FunctionType, -1, "keys", 1, {&protoFnArity_423}};

ProtoImpls *protoImpls_424;
Function protoFn_425;
Value *protoFnImpl_427(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_424);
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
FnArity protoFnArity_428 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_427};
Function protoFn_425 = {FunctionType, -1, "sha1", 1, {&protoFnArity_428}};


// --------- not --------------
Function fn_429;
Value *arityImpl_430(List *closures, Value *arg0) {
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
Function fn_429 = {FunctionType, -1, "not", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_430}}};


// --------- and --------------
Function fn_432;
Value *arityImpl_433(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_434(List *closures, Value *varArgs) {
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
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_256(empty_list, (Value *)&fn_432, rslt4);
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
Function fn_432 = {FunctionType, -1, "and", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_433}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_434}}};


// --------- or --------------
Function fn_436;
Value *arityImpl_437(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_438(List *closures, Value *varArgs) {
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
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_256(empty_list, (Value *)&fn_436, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
return(cond2);
};

// --------- or main body --------------
Function fn_436 = {FunctionType, -1, "or", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_437}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_438}}};


// --------- = --------------
Function fn_440;
Value *arityImpl_441(List *closures, Value *arg0) {
incRef((Value *)&_num_1);
return((Value *)&_num_1);
};

Value *arityImpl_442(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_291(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_443(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;
Value *rslt3 = arityImpl_141(empty_list, arg1);
Value *rslt4 = protoFnImpl_291(empty_list, arg0, rslt3);
dec_and_free(rslt3);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)arg1);
varArgs5 = (List *)listCons((Value *)arg1, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_256(empty_list, (Value *)&fn_440, rslt6);
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
Function fn_440 = {FunctionType, -1, "=", 3, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_441}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_442}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_443}}};


// --------- partial --------------
Function fn_445;

// --------- anon --------------
Function fn_447;
Value *arityImpl_448(List *closures, Value *varArgs) {
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
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_368(empty_list, val2, rslt4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
Value *rslt7 = arityImpl_259(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = protoFnImpl_256(empty_list, val1, rslt7);
incRef(rslt8);
dec_and_free(rslt8);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt8);
};
Value *arityImpl_446(List *closures, Value *varArgs) {
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
arity_2->fn = arityImpl_448;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
Function *fn_447 = malloc_function(1);
fn_447->type = FunctionType;
fn_447->name = "anon";
fn_447->arityCount = 1;
fn_447->arities[0] = arity_2;
return((Value *)fn_447);
};

// --------- partial main body --------------
Function fn_445 = {FunctionType, -1, "partial", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_446}}};

// forward declaration for 'maybe-val'
Value *var_450;

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_45 = {1, -1, 1,"&"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_44 = {1, -1, 9,"<nothing>"};

// --------- flatten_impl --------------
Function fn_452;
Value *arityImpl_473(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- flatten_impl main body --------------
Function fn_452 = {FunctionType, -1, "flatten_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_473}}};

Value *protoImpl_474(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_451 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_474}}};


// --------- flat-map_impl --------------
Function fn_454;
Value *arityImpl_475(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- flat-map_impl main body --------------
Function fn_454 = {FunctionType, -1, "flat-map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_475}}};

Value *protoImpl_476(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_453 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_476}}};


// --------- wrap_impl --------------
Function fn_456;
Value *arityImpl_477(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
if((var_450)->type != FunctionType) {
rslt5 = protoFnImpl_11(empty_list, var_450, arg1);
} else {
FnArity *arity2 = findFnArity(var_450, 1);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)var_450)->name);
  abort();
}
}
return(rslt5);
};


// --------- wrap_impl main body --------------
Function fn_456 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_477}}};

Value *protoImpl_478(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_455 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_478}}};


// --------- apply*_impl --------------
Function fn_458;
Value *arityImpl_479(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- apply*_impl main body --------------
Function fn_458 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_479}}};

Value *protoImpl_480(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_457 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_480}}};


// --------- zero_impl --------------
Function fn_460;
Value *arityImpl_481(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- zero_impl main body --------------
Function fn_460 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_481}}};

Value *protoImpl_482(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_459 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_482}}};


// --------- comp*_impl --------------
Function fn_462;
Value *arityImpl_483(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_27(empty_list, arg1);
Value *cond3;
Value *cond4;
Value *rslt5 = protoFnImpl_203(empty_list, (Value *)&_num_4, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
Value *rslt6 = protoFnImpl_313(empty_list, rslt2);
Value *rslt7 = protoFnImpl_239(empty_list, rslt6, (Value *)&_num_1);
Value *rslt8 = arityImpl_430(empty_list, rslt7);
incRef(rslt8);
cond4 = rslt8;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt7);
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
Value *rslt12 = protoFnImpl_368(empty_list, arg9, arg10);
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
Function fn_462 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_483}}};

Value *protoImpl_487(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_461 = {FunctionType, -1, "comp*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_487}}};


// --------- =*_impl --------------
Function fn_464;
Value *arityImpl_488(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_102(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_464 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_488}}};

Value *protoImpl_489(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_463 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_489}}};


// --------- string-list_impl --------------
Function fn_466;
Value *arityImpl_490(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_44);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_44, varArgs1);
Value *rslt2 = arityImpl_259(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_466 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_490}}};

Value *protoImpl_491(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_465 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_491}}};


// --------- map_impl --------------
Function fn_468;
Value *arityImpl_492(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- map_impl main body --------------
Function fn_468 = {FunctionType, -1, "map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_492}}};

Value *protoImpl_493(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_467 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_493}}};


// --------- type-args_impl --------------
Function fn_470;
Value *arityImpl_494(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- type-args_impl main body --------------
Function fn_470 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_494}}};

Value *protoImpl_495(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_469 = {FunctionType, -1, "type-args", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_495}}};


// --------- invoke_impl --------------
Function fn_472;
Value *arityImpl_496(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- invoke_impl main body --------------
Function fn_472 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_496}}};

Value *protoImpl_497(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_471 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_497}}};

ReifiedVal reified_498 = {13, -1, 11, {(Value *)&fn_452, (Value *)&fn_454, (Value *)&fn_456, (Value *)&fn_458, (Value *)&fn_460, (Value *)&fn_462, (Value *)&fn_464, (Value *)&fn_466, (Value *)&fn_468, (Value *)&fn_470, (Value *)&fn_472}};

// --------- any? --------------
Function fn_500;
Value *arityImpl_501(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt5 = protoFnImpl_319(empty_list, arg1);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt5);
Value *rslt6 = protoFnImpl_342(empty_list, arg1);
Value *rslt10;
if((arg0)->type != FunctionType) {
rslt10 = protoFnImpl_11(empty_list, arg0, rslt6);
} else {
FnArity *arity7 = findFnArity(arg0, 1);
if(arity7 != (FnArity *)0 && !arity7->variadic) {
FnType1 *fn9 = (FnType1 *)arity7->fn;
rslt10 = fn9(arity7->closures, rslt6);
} else if(arity7 != (FnArity *)0 && arity7->variadic) {
FnType1 *fn9 = (FnType1 *)arity7->fn;
List *varArgs8 = empty_list;
incRef(rslt6);
varArgs8 = (List *)listCons(rslt6, varArgs8);
rslt10 = fn9(arity7->closures, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
dec_and_free(rslt6);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef((Value *)&_num_1);
cond2 = (Value *)&_num_1;
} else {
dec_and_free(rslt10);
Value *rslt3 = protoFnImpl_338(empty_list, arg1);
Value *rslt4 = arityImpl_501(closures, arg0, rslt3);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
dec_and_free(rslt3);
}
}
return(cond2);
};


// --------- any? main body --------------
Function fn_500 = {FunctionType, -1, "any?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_501}}};

ProtoImpls *protoImpls_503;
Function protoFn_504;
Value *protoFnImpl_506(List *closures, Value *arg0) {
  Function *implFn = (Function *)findProtoImpl(arg0->type, protoImpls_503);
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
FnArity protoFnArity_507 = {FnArityType, -1, 1, (List *)0, 0, protoFnImpl_506};
Function protoFn_504 = {FunctionType, -1, ".v", 1, {&protoFnArity_507}};

Value *protoFnImpl_509(List *, Value *, Value *);
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[8];} _str_46 = {1, -1, 7,"<maybe "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[10];} _str_48 = {1, -1, 9,"maybe-val"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_47 = {1, -1, 1,">"};
Number _num_14 = {2, -1, 15};

// --------- apply*_impl --------------
Function fn_511;
Value *arityImpl_516(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
incRef((Value *)(Value *)&protoFn_1);
varArgs2 = (List *)listCons((Value *)(Value *)&protoFn_1, varArgs2);
Value *rslt3 = arityImpl_373(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};


// --------- apply*_impl main body --------------
Function fn_511 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_516}}};

Value *protoImpl_517(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_510 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_517}}};


// --------- invoke_impl --------------
Function fn_513;

// --------- flatten_impl --------------
Function fn_520;
Value *arityImpl_541(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val1);
return(val1);
};

Value *protoImpl_542(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_519 = {FunctionType, -1, "flatten", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_542}}};


// --------- flat-map_impl --------------
Function fn_522;
Value *arityImpl_543(List *closures, Value *arg0, Value *arg1) {
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

Value *protoImpl_544(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_521 = {FunctionType, -1, "flat-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_544}}};


// --------- wrap_impl --------------
Function fn_524;
Value *arityImpl_545(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_509(empty_list, var_450, arg1);
return(rslt2);
};


// --------- wrap_impl main body --------------
Function fn_524 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_545}}};

Value *protoImpl_546(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_523 = {FunctionType, -1, "wrap", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_546}}};


// --------- apply*_impl --------------
Function fn_526;
Value *arityImpl_547(List *closures, Value *arg0, Value *arg1) {
Value * val3  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *cond2;
List *varArgs9 = empty_list;
incRef((Value *)(Value *)&reified_498);
varArgs9 = (List *)listCons((Value *)(Value *)&reified_498, varArgs9);
incRef((Value *)(Value *)&fn_440);
varArgs9 = (List *)listCons((Value *)(Value *)&fn_440, varArgs9);
Value *rslt10 = arityImpl_446(empty_list, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
Value *rslt11 = arityImpl_501(empty_list, arg1, rslt10);
dec_and_free(rslt10);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef((Value *)&reified_498);
cond2 = (Value *)&reified_498;
} else {
dec_and_free(rslt11);
Value *rslt4 = protoFnImpl_267(empty_list, arg1, (Value *)&protoFn_504);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_256(empty_list, val3, rslt6);
Value *rslt8 = protoFnImpl_509(empty_list, var_450, rslt7);
incRef(rslt8);
cond2 = rslt8;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
return(cond2);
};

Value *protoImpl_548(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[3])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_525 = {FunctionType, -1, "apply*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_548}}};


// --------- zero_impl --------------
Function fn_528;
Value *arityImpl_549(List *closures, Value *arg0) {
incRef((Value *)&reified_498);
return((Value *)&reified_498);
};


// --------- zero_impl main body --------------
Function fn_528 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_549}}};

Value *protoImpl_550(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[4])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_527 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_550}}};


// --------- comp*_impl --------------
Function fn_530;
Value *arityImpl_551(List *closures, Value *arg0, Value *arg1) {
incRef(arg0);
return(arg0);
};


// --------- comp*_impl main body --------------
Function fn_530 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_551}}};

Value *protoImpl_552(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[5])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_529 = {FunctionType, -1, "comp*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_552}}};


// --------- string-list_impl --------------
Function fn_532;
Value *arityImpl_553(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_46);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_46, varArgs1);
Value *rslt2 = arityImpl_259(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = protoFnImpl_506(empty_list, arg0);
Value *rslt4 = protoFnImpl_279(empty_list, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_47);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_47, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
Value *rslt8 = arityImpl_259(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = protoFnImpl_368(empty_list, rslt2, rslt8);
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
Function fn_532 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_553}}};

Value *protoImpl_554(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[6])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_531 = {FunctionType, -1, "string-list", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_554}}};


// --------- map_impl --------------
Function fn_534;
Value *arityImpl_555(List *closures, Value *arg0, Value *arg1) {
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
Value *rslt7 = protoFnImpl_509(empty_list, var_450, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt7);
return(rslt7);
};

Value *protoImpl_556(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[7])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_533 = {FunctionType, -1, "map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_556}}};


// --------- type-args_impl --------------
Function fn_536;
Value *arityImpl_557(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)val1);
varArgs2 = (List *)listCons((Value *)val1, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};

Value *protoImpl_558(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[8])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_535 = {FunctionType, -1, "type-args", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_558}}};


// --------- type-name_impl --------------
Function fn_538;
Value *arityImpl_559(List *closures, Value *arg0) {
incRef((Value *)&_str_48);
return((Value *)&_str_48);
};


// --------- type-name_impl main body --------------
Function fn_538 = {FunctionType, -1, "type-name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_559}}};

Value *protoImpl_560(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[9])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_537 = {FunctionType, -1, "type-name", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_560}}};


// --------- .v_impl --------------
Function fn_540;
Value *arityImpl_561(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val1);
return(val1);
};

Value *protoImpl_562(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[10])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_539 = {FunctionType, -1, ".v", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_562}}};

Value *arityImpl_518(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_541;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_520 = malloc_function(1);
fn_520->type = FunctionType;
fn_520->name = "flatten_impl";
fn_520->arityCount = 1;
fn_520->arities[0] = arity_2;
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_543;
incRef((Value *)arg1);
arity_3->closures = listCons((Value *)arg1, (List *)arity_3->closures);
Function *fn_522 = malloc_function(1);
fn_522->type = FunctionType;
fn_522->name = "flat-map_impl";
fn_522->arityCount = 1;
fn_522->arities[0] = arity_3;
FnArity *arity_5 = malloc_fnArity();
arity_5->type = FnArityType;
arity_5->count = 2;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_547;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_526 = malloc_function(1);
fn_526->type = FunctionType;
fn_526->name = "apply*_impl";
fn_526->arityCount = 1;
fn_526->arities[0] = arity_5;
FnArity *arity_9 = malloc_fnArity();
arity_9->type = FnArityType;
arity_9->count = 2;
arity_9->closures = empty_list;
arity_9->variadic = 0;
arity_9->fn = arityImpl_555;
incRef((Value *)arg1);
arity_9->closures = listCons((Value *)arg1, (List *)arity_9->closures);
Function *fn_534 = malloc_function(1);
fn_534->type = FunctionType;
fn_534->name = "map_impl";
fn_534->arityCount = 1;
fn_534->arities[0] = arity_9;
FnArity *arity_10 = malloc_fnArity();
arity_10->type = FnArityType;
arity_10->count = 1;
arity_10->closures = empty_list;
arity_10->variadic = 0;
arity_10->fn = arityImpl_557;
incRef((Value *)arg1);
arity_10->closures = listCons((Value *)arg1, (List *)arity_10->closures);
Function *fn_536 = malloc_function(1);
fn_536->type = FunctionType;
fn_536->name = "type-args_impl";
fn_536->arityCount = 1;
fn_536->arities[0] = arity_10;
FnArity *arity_12 = malloc_fnArity();
arity_12->type = FnArityType;
arity_12->count = 1;
arity_12->closures = empty_list;
arity_12->variadic = 0;
arity_12->fn = arityImpl_561;
incRef((Value *)arg1);
arity_12->closures = listCons((Value *)arg1, (List *)arity_12->closures);
Function *fn_540 = malloc_function(1);
fn_540->type = FunctionType;
fn_540->name = ".v_impl";
fn_540->arityCount = 1;
fn_540->arities[0] = arity_12;
Value *reified_13 = (Value *)malloc_reified(11);
((ReifiedVal *)reified_13)->type = 15;
((ReifiedVal *)reified_13)->implCount = 11;
((ReifiedVal *)reified_13)->impls[0] = (Value *)fn_520;
incRef((Value *)fn_520);
((ReifiedVal *)reified_13)->impls[1] = (Value *)fn_522;
incRef((Value *)fn_522);
((ReifiedVal *)reified_13)->impls[2] = (Value *)&fn_524;
incRef((Value *)&fn_524);
((ReifiedVal *)reified_13)->impls[3] = (Value *)fn_526;
incRef((Value *)fn_526);
((ReifiedVal *)reified_13)->impls[4] = (Value *)&fn_528;
incRef((Value *)&fn_528);
((ReifiedVal *)reified_13)->impls[5] = (Value *)&fn_530;
incRef((Value *)&fn_530);
((ReifiedVal *)reified_13)->impls[6] = (Value *)&fn_532;
incRef((Value *)&fn_532);
((ReifiedVal *)reified_13)->impls[7] = (Value *)fn_534;
incRef((Value *)fn_534);
((ReifiedVal *)reified_13)->impls[8] = (Value *)fn_536;
incRef((Value *)fn_536);
((ReifiedVal *)reified_13)->impls[9] = (Value *)&fn_538;
incRef((Value *)&fn_538);
((ReifiedVal *)reified_13)->impls[10] = (Value *)fn_540;
incRef((Value *)fn_540);
incRef(reified_13);
dec_and_free((Value *)fn_536);
dec_and_free((Value *)fn_526);
dec_and_free((Value *)fn_522);
dec_and_free((Value *)fn_540);
dec_and_free(reified_13);
dec_and_free((Value *)fn_534);
dec_and_free((Value *)fn_520);
return(reified_13);
};


// --------- invoke_impl main body --------------
Function fn_513 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_518}}};

Value *protoFnImpl_509(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_512 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoFnImpl_509}}};


// --------- instance?_impl --------------
Function fn_515;
Value *arityImpl_563(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_99(empty_list, arg1);
Value *rslt3 = arityImpl_442(empty_list, (Value *)&_num_14, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- instance?_impl main body --------------
Function fn_515 = {FunctionType, -1, "instance?_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_563}}};

Value *protoImpl_564(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_514 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_564}}};

ReifiedVal reified_565 = {14, -1, 3, {(Value *)&fn_511, (Value *)&fn_513, (Value *)&fn_515}};
Value *var_450 = (Value *)&reified_565;

// --------- zero_impl --------------
Function fn_567;
Value *arityImpl_572(List *closures, Value *arg0) {
incRef((Value *)&reified_498);
return((Value *)&reified_498);
};


// --------- zero_impl main body --------------
Function fn_567 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_572}}};

Value *protoImpl_573(List *closures, Value *arg0) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType1 *)arityPtr->fn)(arityPtr->closures, arg0);
return(rval);
};

Function protoFn_566 = {FunctionType, -1, "zero", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, protoImpl_573}}};


// --------- invoke_impl --------------
Function fn_569;
Value *arityImpl_574(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_509(empty_list, var_450, arg1);
return(rslt2);
};


// --------- invoke_impl main body --------------
Function fn_569 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_574}}};

Value *protoImpl_575(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[1])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_568 = {FunctionType, -1, "invoke", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_575}}};


// --------- instance?_impl --------------
Function fn_571;
Value *arityImpl_576(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoImpl_564(empty_list, var_450, arg1);
return(rslt2);
};


// --------- instance?_impl main body --------------
Function fn_571 = {FunctionType, -1, "instance?_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_576}}};

Value *protoImpl_577(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[2])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_570 = {FunctionType, -1, "instance?", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_577}}};

ReifiedVal reified_578 = {16, -1, 3, {(Value *)&fn_567, (Value *)&fn_569, (Value *)&fn_571}};

// --------- m= --------------
Function fn_580;
Value *arityImpl_581(List *closures, Value *arg0) {
Value *rslt1 = protoImpl_575(empty_list, (Value *)&reified_578, arg0);
return(rslt1);
};

Value *arityImpl_582(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt3 = protoFnImpl_291(empty_list, arg0, arg1);

if (isTrue(rslt3)) {
dec_and_free(rslt3);
Value *rslt4 = protoImpl_575(empty_list, (Value *)&reified_578, arg0);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
} else {
dec_and_free(rslt3);
incRef((Value *)&reified_498);
cond2 = (Value *)&reified_498;
}
return(cond2);
};

Value *arityImpl_583(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *cond2;
Value *rslt3 = arityImpl_141(empty_list, arg1);
Value *rslt4 = protoFnImpl_291(empty_list, arg0, rslt3);
dec_and_free(rslt3);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)arg1);
varArgs5 = (List *)listCons((Value *)arg1, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_256(empty_list, (Value *)&fn_580, rslt6);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
} else {
dec_and_free(rslt4);
incRef((Value *)&reified_498);
cond2 = (Value *)&reified_498;
}
return(cond2);
};

// --------- m= main body --------------
Function fn_580 = {FunctionType, -1, "m=", 3, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_581}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_582}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_583}}};


// --------- some --------------
Function fn_585;
Value *arityImpl_586(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt5 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
incRef((Value *)&reified_498);
cond2 = (Value *)&reified_498;
} else {
dec_and_free(rslt5);
Value *rslt6 = protoFnImpl_342(empty_list, arg0);
Value *rslt10;
if((arg1)->type != FunctionType) {
rslt10 = protoFnImpl_11(empty_list, arg1, rslt6);
} else {
FnArity *arity7 = findFnArity(arg1, 1);
if(arity7 != (FnArity *)0 && !arity7->variadic) {
FnType1 *fn9 = (FnType1 *)arity7->fn;
rslt10 = fn9(arity7->closures, rslt6);
} else if(arity7 != (FnArity *)0 && arity7->variadic) {
FnType1 *fn9 = (FnType1 *)arity7->fn;
List *varArgs8 = empty_list;
incRef(rslt6);
varArgs8 = (List *)listCons(rslt6, varArgs8);
rslt10 = fn9(arity7->closures, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg1)->name);
  abort();
}
}
dec_and_free(rslt6);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
Value *rslt11 = protoFnImpl_342(empty_list, arg0);
Value *rslt12 = protoImpl_575(empty_list, (Value *)&reified_578, rslt11);
incRef(rslt12);
cond2 = rslt12;
dec_and_free(rslt11);
dec_and_free(rslt12);
} else {
dec_and_free(rslt10);
Value *rslt3 = protoFnImpl_338(empty_list, arg0);
Value *rslt4 = arityImpl_586(closures, rslt3, arg1);
incRef(rslt4);
cond2 = rslt4;
dec_and_free(rslt4);
dec_and_free(rslt3);
}
}
return(cond2);
};


// --------- some main body --------------
Function fn_585 = {FunctionType, -1, "some", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_586}}};


// --------- < --------------
Function fn_588;
Value *arityImpl_589(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_239(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_590(List *closures, Value *varArgs) {
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
Value *rslt8 = protoFnImpl_239(empty_list, arg0, rslt7);
Value *rslt9 = arityImpl_430(empty_list, rslt8);
dec_and_free(rslt8);
dec_and_free(rslt7);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt9);
Value *rslt10 = arityImpl_135(empty_list, arg1);
Value *rslt11 = arityImpl_112(empty_list, (Value *)&_num_1, rslt10);
dec_and_free(rslt10);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef((Value *)&_num_1);
cond2 = (Value *)&_num_1;
} else {
dec_and_free(rslt11);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_256(empty_list, (Value *)&fn_588, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
}
}
return(cond2);
};

// --------- < main body --------------
Function fn_588 = {FunctionType, -1, "<", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_589}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_590}}};


// --------- list** --------------
Function fn_592;
Value *arityImpl_593(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt7);
Value *rslt3 = arityImpl_141(empty_list, arg1);
Value *rslt4 = arityImpl_144(empty_list, arg1);
Value *rslt5 = arityImpl_593(closures, rslt3, rslt4);
Value *rslt6 = arityImpl_132(empty_list, arg0, rslt5);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- list** main body --------------
Function fn_592 = {FunctionType, -1, "list**", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_593}}};


// --------- list* --------------
Function fn_595;
Value *arityImpl_596(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = arityImpl_593(empty_list, arg0, arg1);
return(rslt2);
};

// --------- list* main body --------------
Function fn_595 = {FunctionType, -1, "list*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_596}}};


// --------- filter --------------
Function fn_598;
Value *arityImpl_599(List *closures, Value *arg0, Value *arg1) {
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
Function fn_598 = {FunctionType, -1, "filter", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_599}}};


// --------- remove --------------
Function fn_601;

// --------- anon --------------
Function fn_603;
Value *arityImpl_604(List *closures, Value *arg0) {
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
Value *rslt6 = arityImpl_430(empty_list, rslt5);
incRef(rslt6);
dec_and_free(rslt6);
dec_and_free(rslt5);
return(rslt6);
};

Value *arityImpl_602(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 1;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_604;
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_603 = malloc_function(1);
fn_603->type = FunctionType;
fn_603->name = "anon";
fn_603->arityCount = 1;
fn_603->arities[0] = arity_2;
Value *rslt3 = arityImpl_599(empty_list, arg0, (Value *)fn_603);
incRef(rslt3);
dec_and_free((Value *)fn_603);
dec_and_free(rslt3);
return(rslt3);
};


// --------- remove main body --------------
Function fn_601 = {FunctionType, -1, "remove", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_602}}};


// --------- reverse --------------
Function fn_606;
Value *arityImpl_607(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_311(empty_list, arg0);
Value *rslt2 = protoFnImpl_321(empty_list, arg0, rslt1, (Value *)&protoFn_300);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- reverse main body --------------
Function fn_606 = {FunctionType, -1, "reverse", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_607}}};


// --------- identity --------------
Function fn_609;
Value *arityImpl_610(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- identity main body --------------
Function fn_609 = {FunctionType, -1, "identity", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_610}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_49 = {1, -1, 5,"<Fn: "};

// --------- apply*_impl --------------
Function fn_612;
Value *arityImpl_616(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
Value *rslt11;
if((arg0)->type != FunctionType) {
rslt11 = protoFnImpl_9(empty_list, arg0);
} else {
FnArity *arity8 = findFnArity(arg0, 0);
if(arity8 != (FnArity *)0 && !arity8->variadic) {
FnType0 *fn10 = (FnType0 *)arity8->fn;
rslt11 = fn10(arity8->closures);
} else if(arity8 != (FnArity *)0 && arity8->variadic) {
FnType1 *fn10 = (FnType1 *)arity8->fn;
List *varArgs9 = empty_list;
rslt11 = fn10(arity8->closures, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg0)->name);
  abort();
}
}
incRef(rslt11);
cond2 = rslt11;
dec_and_free(rslt11);
} else {
dec_and_free(rslt7);
Value *rslt3 = protoFnImpl_342(empty_list, arg1);
Value *rslt4 = protoFnImpl_338(empty_list, arg1);
Value *rslt5 = arityImpl_593(empty_list, rslt3, rslt4);
Value *rslt6 = arityImpl_174(empty_list, arg0, rslt5);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- apply*_impl main body --------------
Function fn_612 = {FunctionType, -1, "apply*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_616}}};


// --------- zero_impl --------------
Function fn_613;
Value *arityImpl_617(List *closures, Value *arg0) {
incRef((Value *)&fn_609);
return((Value *)&fn_609);
};


// --------- zero_impl main body --------------
Function fn_613 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_617}}};


// --------- comp*_impl --------------
Function fn_614;

// --------- anon --------------
Function fn_619;

// --------- anon --------------
Function fn_621;
Value *arityImpl_622(List *closures, Value *arg0, Value *arg1) {
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
Function fn_621 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_622}}};

Value *arityImpl_620(List *closures, Value *varArgs) {
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
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = protoFnImpl_256(empty_list, val2, rslt4);
Value *rslt7 = protoFnImpl_321(empty_list, val1, rslt5, (Value *)&fn_621);
incRef(rslt7);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt7);
};
Value *arityImpl_618(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 2;
arity_2->closures = empty_list;
arity_2->variadic = 1;
arity_2->fn = arityImpl_620;
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_619 = malloc_function(1);
fn_619->type = FunctionType;
fn_619->name = "anon";
fn_619->arityCount = 1;
fn_619->arities[0] = arity_2;
return((Value *)fn_619);
};


// --------- comp*_impl main body --------------
Function fn_614 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_618}}};


// --------- string-list_impl --------------
Function fn_615;
Value *arityImpl_623(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_147(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)(Value *)&_str_47);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_47, varArgs2);
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)(Value *)&_str_49);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_49, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_615 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_623}}};


// --------- sha1_impl --------------
Function fn_624;
Value *arityImpl_628(List *closures, Value *arg0) {

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
Function fn_624 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_628}}};


// --------- <*_impl --------------
Function fn_625;
Value *arityImpl_629(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_115(empty_list, arg0, arg1);
return(rslt2);
};


// --------- <*_impl main body --------------
Function fn_625 = {FunctionType, -1, "<*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_629}}};


// --------- =*_impl --------------
Function fn_626;
Value *arityImpl_630(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_112(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_626 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_630}}};


// --------- string-list_impl --------------
Function fn_627;
Value *arityImpl_631(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_109(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_627 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_631}}};


// --------- comprehend --------------
Function fn_633;
Value *arityImpl_634(List *closures, Value *arg0) {
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


// --------- anon --------------
Function fn_636;
Value *arityImpl_638(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val3  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4 = arityImpl_132(empty_list, arg1, arg0);
Value *rslt5 = arityImpl_607(empty_list, rslt4);
List *varArgs6 = empty_list;
incRef((Value *)rslt5);
varArgs6 = (List *)listCons((Value *)rslt5, varArgs6);
Value *rslt7 = arityImpl_259(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
Value *rslt8 = protoFnImpl_256(empty_list, val3, rslt7);
Value *rslt9 = protoFnImpl_249(empty_list, val2, rslt8);
incRef(rslt9);
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt9);
};


// --------- anon --------------
Function fn_637;

// --------- anon --------------
Function fn_640;
Value *arityImpl_641(List *closures, Value *arg0, Value *arg1) {
Value * val2  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value * val3  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt4 = arityImpl_132(empty_list, arg1, arg0);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)val3);
varArgs5 = (List *)listCons((Value *)val3, varArgs5);
Value *rslt6 = arityImpl_446(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = protoFnImpl_212(empty_list, val2, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt4);
dec_and_free(rslt7);
return(rslt7);
};

Value *arityImpl_639(List *closures, Value *arg0, Value *arg1) {
FnArity *arity_2 = malloc_fnArity();
arity_2->type = FnArityType;
arity_2->count = 2;
arity_2->closures = empty_list;
arity_2->variadic = 0;
arity_2->fn = arityImpl_641;
incRef((Value *)arg0);
arity_2->closures = listCons((Value *)arg0, (List *)arity_2->closures);
incRef((Value *)arg1);
arity_2->closures = listCons((Value *)arg1, (List *)arity_2->closures);
Function *fn_640 = malloc_function(1);
fn_640->type = FunctionType;
fn_640->name = "anon";
fn_640->arityCount = 1;
fn_640->arities[0] = arity_2;
return((Value *)fn_640);
};


// --------- anon main body --------------
Function fn_637 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_639}}};


// --------- anon --------------
Function fn_642;
Value *arityImpl_643(List *closures, Value *arg0) {
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
Value *rslt7 = protoFnImpl_249(empty_list, val1, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt7);
return(rslt7);
};

Value *arityImpl_635(List *closures, Value *arg0, Value *arg3) {
List *arg4 = (List *)arg3;
Value *arg1 = arg4->head;
if (arg4->tail) arg4->tail->len = arg4->len - 1;
arg4 = arg4->tail;
Value *arg2 = (Value *) arg4;
Value *rslt5 = arityImpl_607(empty_list, arg2);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 2;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_638;
incRef((Value *)arg0);
arity_6->closures = listCons((Value *)arg0, (List *)arity_6->closures);
incRef((Value *)arg1);
arity_6->closures = listCons((Value *)arg1, (List *)arity_6->closures);
Function *fn_636 = malloc_function(1);
fn_636->type = FunctionType;
fn_636->name = "anon";
fn_636->arityCount = 1;
fn_636->arities[0] = arity_6;
Value *rslt8 = protoFnImpl_321(empty_list, rslt5, (Value *)fn_636, (Value *)&fn_637);
Value *cond9;
Value *rslt13 = arityImpl_135(empty_list, arg2);
Value *rslt14 = arityImpl_112(empty_list, (Value *)&_num_1, rslt13);
dec_and_free(rslt13);

if (isTrue(rslt14)) {
dec_and_free(rslt14);
FnArity *arity_15 = malloc_fnArity();
arity_15->type = FnArityType;
arity_15->count = 1;
arity_15->closures = empty_list;
arity_15->variadic = 0;
arity_15->fn = arityImpl_643;
incRef((Value *)arg0);
arity_15->closures = listCons((Value *)arg0, (List *)arity_15->closures);
incRef((Value *)arg1);
arity_15->closures = listCons((Value *)arg1, (List *)arity_15->closures);
Function *fn_642 = malloc_function(1);
fn_642->type = FunctionType;
fn_642->name = "anon";
fn_642->arityCount = 1;
fn_642->arities[0] = arity_15;
Value *rslt16 = protoFnImpl_212(empty_list, arg1, (Value *)fn_642);
incRef(rslt16);
cond9 = rslt16;
dec_and_free((Value *)fn_642);
dec_and_free(rslt16);
} else {
dec_and_free(rslt14);
List *varArgs10 = empty_list;
incRef((Value *)var_129);
varArgs10 = (List *)listCons((Value *)var_129, varArgs10);
incRef((Value *)rslt8);
varArgs10 = (List *)listCons((Value *)rslt8, varArgs10);
Value *rslt11 = arityImpl_446(empty_list, (Value *)varArgs10);
dec_and_free((Value *)varArgs10);
Value *rslt12 = protoFnImpl_212(empty_list, arg1, rslt11);
incRef(rslt12);
cond9 = rslt12;
dec_and_free(rslt11);
dec_and_free(rslt12);
}
incRef(cond9);
dec_and_free(rslt8);
dec_and_free(cond9);
dec_and_free((Value *)fn_636);
dec_and_free(rslt5);
return(cond9);
};


// --------- comprehend main body --------------
Function fn_633 = {FunctionType, -1, "comprehend", 2, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_634}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_635}}};

Value *var_241 = (Value *)&fn_633;

// --------- list-concat --------------
Function fn_644;
Value *arityImpl_645(List *closures, Value *arg0) {
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
Function fn_644 = {FunctionType, -1, "list-concat", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_645}}};


// --------- list=* --------------
Function fn_647;

// --------- anon --------------
Function fn_649;
Value *arityImpl_650(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_141(empty_list, arg0);
return(rslt1);
};


// --------- anon main body --------------
Function fn_649 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_650}}};

Value *arityImpl_648(List *closures, Value *arg0) {
Value *cond1;
Value *rslt4 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef((Value *)&_num_1);
cond1 = (Value *)&_num_1;
} else {
dec_and_free(rslt4);
Value *rslt5 = arityImpl_141(empty_list, arg0);
Value *rslt6 = arityImpl_138(empty_list, rslt5);
dec_and_free(rslt5);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef((Value *)&_num_1);
cond1 = (Value *)&_num_1;
} else {
dec_and_free(rslt6);
Value *rslt8 = protoFnImpl_267(empty_list, arg0, (Value *)&fn_649);
List *varArgs9 = empty_list;
incRef((Value *)rslt8);
varArgs9 = (List *)listCons((Value *)rslt8, varArgs9);
Value *rslt10 = arityImpl_259(empty_list, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
Value *rslt11 = arityImpl_616(empty_list, (Value *)&fn_440, rslt10);
Value *rslt12 = arityImpl_430(empty_list, rslt11);
dec_and_free(rslt8);
dec_and_free(rslt10);
dec_and_free(rslt11);

if (isTrue(rslt12)) {
dec_and_free(rslt12);
incRef((Value *)&_num_13);
cond1 = (Value *)&_num_13;
} else {
dec_and_free(rslt12);
Value *rslt2 = protoFnImpl_267(empty_list, arg0, (Value *)&protoFn_324);
Value *rslt3 = arityImpl_648(closures, rslt2);
incRef(rslt3);
cond1 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
}
}
return(cond1);
};


// --------- list=* main body --------------
Function fn_647 = {FunctionType, -1, "list=*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_648}}};


// --------- reduce-list --------------
Function fn_652;
Value *arityImpl_653(List *closures, Value *arg2, Value *arg4, Value *arg5) {
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
Value *rslt13 = protoFnImpl_313(empty_list, rslt6);
Value *rslt14 = protoFnImpl_239(empty_list, rslt13, (Value *)&_num_1);
Value *rslt15 = arityImpl_430(empty_list, rslt14);
incRef(rslt15);
cond12 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(rslt13);
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
Value *rslt23 = arityImpl_653(closures, arg1, rslt22, arg5);
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
Function fn_652 = {FunctionType, -1, "reduce-list", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_653}}};


// --------- traverse_impl --------------
Function fn_658;
Value *arityImpl_677(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_267(empty_list, arg0, arg1);
Value *rslt3 = protoFnImpl_27(empty_list, rslt2);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_203(empty_list, (Value *)&_num_4, rslt2);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *rslt7 = protoFnImpl_313(empty_list, rslt3);
Value *rslt8 = protoFnImpl_239(empty_list, rslt7, (Value *)&_num_1);
Value *rslt9 = arityImpl_430(empty_list, rslt8);
incRef(rslt9);
cond5 = rslt9;
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt7);
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
Value *rslt13 = protoFnImpl_249(empty_list, arg10, (Value *)&fn_258);
Value *rslt14 = arityImpl_132(empty_list, arg10, arg11);
Value *rslt15 = protoFnImpl_256(empty_list, rslt13, rslt14);
incRef(rslt15);
cond4 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(rslt13);
} else {
dec_and_free(cond5);
incRef((Value *)&reified_498);
cond4 = (Value *)&reified_498;
}
incRef(cond4);
dec_and_free(cond4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(cond4);
};


// --------- traverse_impl main body --------------
Function fn_658 = {FunctionType, -1, "traverse_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_677}}};


// --------- empty?_impl --------------
Function fn_659;
Value *arityImpl_681(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_138(empty_list, arg0);
return(rslt1);
};


// --------- empty?_impl main body --------------
Function fn_659 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_681}}};


// --------- empty_impl --------------
Function fn_660;
Value *arityImpl_682(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- empty_impl main body --------------
Function fn_660 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_682}}};


// --------- conj_impl --------------
Function fn_661;
Value *arityImpl_683(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_132(empty_list, arg1, arg0);
return(rslt2);
};


// --------- conj_impl main body --------------
Function fn_661 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_683}}};


// --------- count_impl --------------
Function fn_662;
Value *arityImpl_684(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_135(empty_list, arg0);
return(rslt1);
};


// --------- count_impl main body --------------
Function fn_662 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_684}}};


// --------- reduce_impl --------------
Function fn_663;
Value *arityImpl_685(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_27(empty_list, arg0);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_203(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *rslt7 = protoFnImpl_313(empty_list, rslt3);
Value *rslt8 = protoFnImpl_239(empty_list, rslt7, (Value *)&_num_1);
Value *rslt9 = arityImpl_430(empty_list, rslt8);
incRef(rslt9);
cond5 = rslt9;
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt7);
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
Value *rslt13 = arityImpl_653(empty_list, arg0, arg1, arg2);
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
Function fn_663 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_685}}};


// --------- crush_impl --------------
Function fn_664;

// --------- anon --------------
Function fn_690;
Value *arityImpl_691(List *closures, Value *arg0, Value *arg1) {
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
Value *rslt8 = arityImpl_259(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = protoFnImpl_368(empty_list, arg0, rslt8);
incRef(rslt9);
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt9);
return(rslt9);
};

Value *arityImpl_689(List *closures, Value *arg0, Value *arg1) {
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
arity_8->fn = arityImpl_691;
incRef((Value *)arg1);
arity_8->closures = listCons((Value *)arg1, (List *)arity_8->closures);
Function *fn_690 = malloc_function(1);
fn_690->type = FunctionType;
fn_690->name = "anon";
fn_690->arityCount = 1;
fn_690->arities[0] = arity_8;
Value *rslt9 = arityImpl_685(empty_list, rslt2, rslt7, (Value *)fn_690);
incRef(rslt9);
dec_and_free((Value *)fn_690);
dec_and_free(rslt9);
dec_and_free(rslt7);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt9);
};


// --------- crush_impl main body --------------
Function fn_664 = {FunctionType, -1, "crush_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_689}}};


// --------- flat-map_impl --------------
Function fn_665;
Value *arityImpl_692(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_267(empty_list, arg0, arg1);
Value *rslt3 = protoFnImpl_27(empty_list, rslt2);
Value *cond4;
Value *cond5;
Value *rslt6 = protoFnImpl_203(empty_list, (Value *)&_num_4, rslt2);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
Value *rslt7 = protoFnImpl_313(empty_list, rslt3);
Value *rslt8 = protoFnImpl_239(empty_list, rslt7, (Value *)&_num_1);
Value *rslt9 = arityImpl_430(empty_list, rslt8);
incRef(rslt9);
cond5 = rslt9;
dec_and_free(rslt8);
dec_and_free(rslt9);
dec_and_free(rslt7);
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
Value *rslt13 = protoFnImpl_368(empty_list, arg10, arg11);
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
Function fn_665 = {FunctionType, -1, "flat-map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_692}}};


// --------- wrap_impl --------------
Function fn_666;
Value *arityImpl_696(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};


// --------- wrap_impl main body --------------
Function fn_666 = {FunctionType, -1, "wrap_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_696}}};


// --------- zero_impl --------------
Function fn_667;
Value *arityImpl_697(List *closures, Value *arg0) {
incRef(var_129);
return(var_129);
};


// --------- zero_impl main body --------------
Function fn_667 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_697}}};


// --------- comp*_impl --------------
Function fn_668;
Value *arityImpl_698(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt3 = arityImpl_645(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_668 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_698}}};


// --------- =*_impl --------------
Function fn_669;
Value *arityImpl_699(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt6 = arityImpl_99(empty_list, arg0);
Value *rslt7 = arityImpl_99(empty_list, arg1);
Value *rslt8 = arityImpl_112(empty_list, rslt6, rslt7);
Value *rslt9 = arityImpl_430(empty_list, rslt8);
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt7);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt9);
Value *rslt10 = protoFnImpl_313(empty_list, arg0);
Value *rslt11 = protoFnImpl_313(empty_list, arg1);
Value *rslt12 = arityImpl_112(empty_list, rslt10, rslt11);
Value *rslt13 = arityImpl_430(empty_list, rslt12);
dec_and_free(rslt10);
dec_and_free(rslt11);
dec_and_free(rslt12);

if (isTrue(rslt13)) {
dec_and_free(rslt13);
incRef((Value *)&_num_13);
cond2 = (Value *)&_num_13;
} else {
dec_and_free(rslt13);
List *varArgs3 = empty_list;
incRef((Value *)arg1);
varArgs3 = (List *)listCons((Value *)arg1, varArgs3);
incRef((Value *)arg0);
varArgs3 = (List *)listCons((Value *)arg0, varArgs3);
Value *rslt4 = arityImpl_259(empty_list, (Value *)varArgs3);
dec_and_free((Value *)varArgs3);
Value *rslt5 = arityImpl_648(empty_list, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
}
}
return(cond2);
};


// --------- =*_impl main body --------------
Function fn_669 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_699}}};


// --------- seq?_impl --------------
Function fn_670;
Value *arityImpl_700(List *closures, Value *arg0) {
incRef(var_75);
return(var_75);
};


// --------- seq?_impl main body --------------
Function fn_670 = {FunctionType, -1, "seq?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_700}}};


// --------- seq_impl --------------
Function fn_671;
Value *arityImpl_701(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- seq_impl main body --------------
Function fn_671 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_701}}};


// --------- m-first_impl --------------
Function fn_672;
Value *arityImpl_702(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_27(empty_list, arg0);
Value *cond2;
Value *cond3;
Value *rslt4 = protoFnImpl_203(empty_list, (Value *)&_num_4, arg0);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
Value *rslt5 = protoFnImpl_313(empty_list, rslt1);
Value *rslt6 = protoFnImpl_239(empty_list, rslt5, (Value *)&_num_1);
Value *rslt7 = arityImpl_430(empty_list, rslt6);
incRef(rslt7);
cond3 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt7);
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
Value *rslt11 = protoImpl_575(empty_list, (Value *)&reified_578, arg8);
incRef(rslt11);
cond2 = rslt11;
dec_and_free(rslt11);
} else {
dec_and_free(cond3);
incRef((Value *)&reified_498);
cond2 = (Value *)&reified_498;
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};


// --------- m-first_impl main body --------------
Function fn_672 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_702}}};


// --------- first_impl --------------
Function fn_673;
Value *arityImpl_706(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_141(empty_list, arg0);
return(rslt1);
};


// --------- first_impl main body --------------
Function fn_673 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_706}}};


// --------- rest_impl --------------
Function fn_674;
Value *arityImpl_707(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_144(empty_list, arg0);
return(rslt1);
};


// --------- rest_impl main body --------------
Function fn_674 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_707}}};


// --------- map_impl --------------
Function fn_675;
Value *arityImpl_708(List *closures, Value *arg0, Value *arg1) {
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
Function fn_675 = {FunctionType, -1, "map_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_708}}};


// --------- type-args_impl --------------
Function fn_676;
Value *arityImpl_709(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};


// --------- type-args_impl main body --------------
Function fn_676 = {FunctionType, -1, "type-args_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_709}}};


// --------- interpose --------------
Function fn_710;

// --------- anon --------------
Function fn_712;
Value *arityImpl_713(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
List *varArgs2 = empty_list;
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
incRef((Value *)val1);
varArgs2 = (List *)listCons((Value *)val1, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
return(rslt3);
};

Value *arityImpl_711(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt8 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt8);
Value *rslt3 = arityImpl_141(empty_list, arg0);
Value *rslt4 = arityImpl_144(empty_list, arg0);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = FnArityType;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_713;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_712 = malloc_function(1);
fn_712->type = FunctionType;
fn_712->name = "anon";
fn_712->arityCount = 1;
fn_712->arities[0] = arity_5;
Value *rslt6 = arityImpl_692(empty_list, rslt4, (Value *)fn_712);
Value *rslt7 = arityImpl_132(empty_list, rslt3, rslt6);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free((Value *)fn_712);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- interpose main body --------------
Function fn_710 = {FunctionType, -1, "interpose", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_711}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_51 = {1, -1, 2,", "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_50 = {1, -1, 1,"("};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_52 = {1, -1, 1,")"};

// --------- string-list_impl --------------
Function fn_715;
Value *arityImpl_716(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)(Value *)&_str_50);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_50, varArgs1);
Value *rslt2 = arityImpl_259(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_711(empty_list, arg0, (Value *)&_str_51);
Value *rslt4 = protoFnImpl_212(empty_list, rslt3, (Value *)&protoFn_276);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_52);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_52, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
List *varArgs7 = empty_list;
incRef((Value *)rslt6);
varArgs7 = (List *)listCons((Value *)rslt6, varArgs7);
incRef((Value *)rslt4);
varArgs7 = (List *)listCons((Value *)rslt4, varArgs7);
incRef((Value *)rslt2);
varArgs7 = (List *)listCons((Value *)rslt2, varArgs7);
Value *rslt8 = arityImpl_259(empty_list, (Value *)varArgs7);
dec_and_free((Value *)varArgs7);
Value *rslt9 = arityImpl_645(empty_list, rslt8);
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
Function fn_715 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_716}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_53 = {1, -1, 1," "};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_54 = {1, -1, 1,"\n"};

// --------- prn --------------
Function fn_717;
Value *arityImpl_718(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_692(empty_list, arg0, (Value *)&protoFn_282);
Value *rslt2 = arityImpl_711(empty_list, rslt1, (Value *)&_str_53);
Value *rslt3 = protoFnImpl_267(empty_list, rslt2, (Value *)&fn_179);
Value *rslt4 = arityImpl_180(empty_list, (Value *)&_str_54);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- prn main body --------------
Function fn_717 = {FunctionType, -1, "prn", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_718}}};


// --------- print --------------
Function fn_720;
Value *arityImpl_721(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_711(empty_list, arg0, (Value *)&_str_53);
Value *rslt2 = protoFnImpl_212(empty_list, rslt1, (Value *)&protoFn_276);
Value *rslt3 = protoFnImpl_267(empty_list, rslt2, (Value *)&fn_179);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};

// --------- print main body --------------
Function fn_720 = {FunctionType, -1, "print", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_721}}};


// --------- println --------------
Function fn_723;
Value *arityImpl_724(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_711(empty_list, arg0, (Value *)&_str_53);
Value *rslt2 = protoFnImpl_212(empty_list, rslt1, (Value *)&protoFn_276);
Value *rslt3 = protoFnImpl_267(empty_list, rslt2, (Value *)&fn_179);
Value *rslt4 = arityImpl_180(empty_list, (Value *)&_str_54);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};

// --------- println main body --------------
Function fn_723 = {FunctionType, -1, "println", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_724}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[6];} _str_55 = {1, -1, 5,"\n*** "};

// --------- print-err --------------
Function fn_727;
Value *arityImpl_728(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_168(empty_list, (Value *)&_str_55);
Value *rslt2 = arityImpl_711(empty_list, arg0, (Value *)&_str_53);
Value *rslt3 = protoFnImpl_212(empty_list, rslt2, (Value *)&protoFn_276);
Value *rslt4 = protoFnImpl_267(empty_list, rslt3, (Value *)&fn_167);
Value *rslt5 = arityImpl_168(empty_list, (Value *)&_str_54);
incRef(rslt5);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt5);
};

// --------- print-err main body --------------
Function fn_727 = {FunctionType, -1, "print-err", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_728}}};

Value *var_53 = (Value *)&fn_727;

// --------- inc --------------
Function fn_729;
Value *arityImpl_730(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_118(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- inc main body --------------
Function fn_729 = {FunctionType, -1, "inc", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_730}}};


// --------- + --------------
Function fn_732;
Value *arityImpl_733(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_734(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_118(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_735(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_685(empty_list, arg0, (Value *)&_num_13, (Value *)&fn_117);
return(rslt1);
};

// --------- + main body --------------
Function fn_732 = {FunctionType, -1, "+", 3, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_733}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_734}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_735}}};


// --------- * --------------
Function fn_737;
Value *arityImpl_738(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_739(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_124(empty_list, arg0, arg1);
return(rslt2);
};

Value *arityImpl_740(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_685(empty_list, arg0, (Value *)&_num_13, (Value *)&fn_123);
return(rslt1);
};

// --------- * main body --------------
Function fn_737 = {FunctionType, -1, "*", 3, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_738}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_739}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_740}}};


// --------- dec --------------
Function fn_742;
Value *arityImpl_743(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_121(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- dec main body --------------
Function fn_742 = {FunctionType, -1, "dec", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_743}}};


// --------- - --------------
Function fn_745;
Value *arityImpl_746(List *closures) {
incRef((Value *)&_num_13);
return((Value *)&_num_13);
};

Value *arityImpl_747(List *closures, Value *arg0) {
incRef(arg0);
return(arg0);
};

Value *arityImpl_748(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = (Value *) argsList;
Value *rslt2 = arityImpl_685(empty_list, arg1, arg0, (Value *)&fn_120);
return(rslt2);
};

// --------- - main body --------------
Function fn_745 = {FunctionType, -1, "-", 3, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_746}, &(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_747}, &(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_748}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[1];} _str_56 = {1, -1, 0,""};

// --------- sha1_impl --------------
Function fn_750;
Value *arityImpl_763(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
String *strVal = (String *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)strVal->buffer, strVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_750 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_763}}};


// --------- empty?_impl --------------
Function fn_751;
Value *arityImpl_764(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
Value *rslt2 = arityImpl_442(empty_list, (Value *)&_num_13, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- empty?_impl main body --------------
Function fn_751 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_764}}};


// --------- empty_impl --------------
Function fn_752;
Value *arityImpl_765(List *closures, Value *arg0) {
incRef((Value *)&_str_56);
return((Value *)&_str_56);
};


// --------- empty_impl main body --------------
Function fn_752 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_765}}};


// --------- count_impl --------------
Function fn_753;
Value *arityImpl_766(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
return(rslt1);
};


// --------- count_impl main body --------------
Function fn_753 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_766}}};


// --------- conj_impl --------------
Function fn_754;
Value *arityImpl_767(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_692(empty_list, rslt3, (Value *)&protoFn_276);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_368(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- conj_impl main body --------------
Function fn_754 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_767}}};


// --------- reduce_impl --------------
Function fn_755;
Value *arityImpl_768(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_340(empty_list, arg0);
Value *rslt4 = protoFnImpl_321(empty_list, rslt3, arg1, arg2);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- reduce_impl main body --------------
Function fn_755 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_768}}};


// --------- comp*_impl --------------
Function fn_756;

// --------- anon --------------
Function fn_770;
Value *arityImpl_771(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_153(empty_list, arg1);
Value *rslt3 = arityImpl_118(empty_list, arg0, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- anon main body --------------
Function fn_770 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_771}}};


// --------- anon --------------
Function fn_772;
Value *arityImpl_773(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = arityImpl_165(empty_list, val1, arg0);
incRef((Value *)&_num_13);
dec_and_free(rslt2);
return((Value *)&_num_13);
};

Value *arityImpl_769(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt10 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt10);
Value *rslt3 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt4 = arityImpl_692(empty_list, rslt3, (Value *)&protoFn_276);
Value *rslt6 = arityImpl_685(empty_list, rslt4, (Value *)&_num_13, (Value *)&fn_770);
Value *rslt7 = arityImpl_162(empty_list, rslt6);
FnArity *arity_8 = malloc_fnArity();
arity_8->type = FnArityType;
arity_8->count = 1;
arity_8->closures = empty_list;
arity_8->variadic = 0;
arity_8->fn = arityImpl_773;
incRef((Value *)rslt7);
arity_8->closures = listCons((Value *)rslt7, (List *)arity_8->closures);
Function *fn_772 = malloc_function(1);
fn_772->type = FunctionType;
fn_772->name = "anon";
fn_772->arityCount = 1;
fn_772->arities[0] = arity_8;
Value *rslt9 = arityImpl_708(empty_list, rslt4, (Value *)fn_772);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free((Value *)fn_772);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- comp*_impl main body --------------
Function fn_756 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_769}}};


// --------- =*_impl --------------
Function fn_757;
Value *arityImpl_774(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_156(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_757 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_774}}};


// --------- string-list_impl --------------
Function fn_758;
Value *arityImpl_775(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_259(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_758 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_775}}};


// --------- seq_impl --------------
Function fn_759;
Value *arityImpl_776(List *closures, Value *arg0) {
Value *cond1;
Value *rslt6 = arityImpl_442(empty_list, arg0, (Value *)&_str_56);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_129);
cond1 = var_129;
} else {
dec_and_free(rslt6);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
Value *rslt4 = protoFnImpl_340(empty_list, rslt3);
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
Function fn_759 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_776}}};


// --------- m-first_impl --------------
Function fn_760;
Value *arityImpl_777(List *closures, Value *arg0) {
Value *cond1;
Value *rslt4 = arityImpl_442(empty_list, arg0, (Value *)&_str_56);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef((Value *)&reified_498);
cond1 = (Value *)&reified_498;
} else {
dec_and_free(rslt4);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = protoImpl_575(empty_list, (Value *)&reified_578, rslt2);
incRef(rslt3);
cond1 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- m-first_impl main body --------------
Function fn_760 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_777}}};


// --------- first_impl --------------
Function fn_761;
Value *arityImpl_778(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
return(rslt1);
};


// --------- first_impl main body --------------
Function fn_761 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_778}}};


// --------- rest_impl --------------
Function fn_762;
Value *arityImpl_779(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- rest_impl main body --------------
Function fn_762 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_779}}};


// --------- sha1_impl --------------
Function fn_780;
Value *arityImpl_793(List *closures, Value *arg0) {

int64_t shaVal;
Sha1Context context;
SubString *subStrVal = (SubString *)arg0;

Sha1Initialise(&context);
Sha1Update(&context, (void *)subStrVal->buffer, subStrVal->len);
Sha1Finalise(&context, (SHA1_HASH *)&shaVal);
return((Value *)numberValue(shaVal));
};


// --------- sha1_impl main body --------------
Function fn_780 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_793}}};


// --------- empty?_impl --------------
Function fn_781;
Value *arityImpl_794(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
Value *rslt2 = arityImpl_442(empty_list, (Value *)&_num_13, rslt1);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- empty?_impl main body --------------
Function fn_781 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_794}}};


// --------- empty_impl --------------
Function fn_782;
Value *arityImpl_795(List *closures, Value *arg0) {
incRef((Value *)&_str_56);
return((Value *)&_str_56);
};


// --------- empty_impl main body --------------
Function fn_782 = {FunctionType, -1, "empty_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_795}}};


// --------- count_impl --------------
Function fn_783;
Value *arityImpl_796(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_153(empty_list, arg0);
return(rslt1);
};


// --------- count_impl main body --------------
Function fn_783 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_796}}};


// --------- conj_impl --------------
Function fn_784;
Value *arityImpl_797(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_692(empty_list, rslt3, (Value *)&protoFn_276);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_368(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- conj_impl main body --------------
Function fn_784 = {FunctionType, -1, "conj_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_797}}};


// --------- reduce_impl --------------
Function fn_785;
Value *arityImpl_798(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_340(empty_list, arg0);
Value *rslt4 = protoFnImpl_321(empty_list, rslt3, arg1, arg2);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- reduce_impl main body --------------
Function fn_785 = {FunctionType, -1, "reduce_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_798}}};


// --------- comp*_impl --------------
Function fn_786;

// --------- anon --------------
Function fn_800;
Value *arityImpl_801(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_153(empty_list, arg1);
Value *rslt3 = arityImpl_118(empty_list, arg0, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- anon main body --------------
Function fn_800 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_801}}};


// --------- anon --------------
Function fn_802;
Value *arityImpl_803(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = arityImpl_165(empty_list, val1, arg0);
incRef((Value *)&_num_13);
dec_and_free(rslt2);
return((Value *)&_num_13);
};

Value *arityImpl_799(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt10 = arityImpl_138(empty_list, arg1);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt10);
Value *rslt3 = arityImpl_132(empty_list, arg0, arg1);
Value *rslt4 = arityImpl_692(empty_list, rslt3, (Value *)&protoFn_276);
Value *rslt6 = arityImpl_685(empty_list, rslt4, (Value *)&_num_13, (Value *)&fn_800);
Value *rslt7 = arityImpl_162(empty_list, rslt6);
FnArity *arity_8 = malloc_fnArity();
arity_8->type = FnArityType;
arity_8->count = 1;
arity_8->closures = empty_list;
arity_8->variadic = 0;
arity_8->fn = arityImpl_803;
incRef((Value *)rslt7);
arity_8->closures = listCons((Value *)rslt7, (List *)arity_8->closures);
Function *fn_802 = malloc_function(1);
fn_802->type = FunctionType;
fn_802->name = "anon";
fn_802->arityCount = 1;
fn_802->arities[0] = arity_8;
Value *rslt9 = arityImpl_708(empty_list, rslt4, (Value *)fn_802);
incRef(rslt7);
cond2 = rslt7;
dec_and_free(rslt6);
dec_and_free((Value *)fn_802);
dec_and_free(rslt9);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- comp*_impl main body --------------
Function fn_786 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_799}}};


// --------- =*_impl --------------
Function fn_787;
Value *arityImpl_804(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_156(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_787 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_804}}};


// --------- string-list_impl --------------
Function fn_788;
Value *arityImpl_805(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
Value *rslt2 = arityImpl_259(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
return(rslt2);
};


// --------- string-list_impl main body --------------
Function fn_788 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_805}}};


// --------- seq_impl --------------
Function fn_789;
Value *arityImpl_806(List *closures, Value *arg0) {
Value *cond1;
Value *rslt6 = arityImpl_442(empty_list, arg0, (Value *)&_str_56);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(var_129);
cond1 = var_129;
} else {
dec_and_free(rslt6);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
Value *rslt4 = protoFnImpl_340(empty_list, rslt3);
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
Function fn_789 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_806}}};


// --------- m-first_impl --------------
Function fn_790;
Value *arityImpl_807(List *closures, Value *arg0) {
Value *cond1;
Value *rslt4 = arityImpl_442(empty_list, arg0, (Value *)&_str_56);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
incRef((Value *)&reified_498);
cond1 = (Value *)&reified_498;
} else {
dec_and_free(rslt4);
Value *rslt2 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
Value *rslt3 = protoImpl_575(empty_list, (Value *)&reified_578, rslt2);
incRef(rslt3);
cond1 = rslt3;
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- m-first_impl main body --------------
Function fn_790 = {FunctionType, -1, "m-first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_807}}};


// --------- first_impl --------------
Function fn_791;
Value *arityImpl_808(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_106(empty_list, arg0, (Value *)&_num_13, (Value *)&_num_1);
return(rslt1);
};


// --------- first_impl main body --------------
Function fn_791 = {FunctionType, -1, "first_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_808}}};


// --------- rest_impl --------------
Function fn_792;
Value *arityImpl_809(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_105(empty_list, arg0, (Value *)&_num_1);
return(rslt1);
};


// --------- rest_impl main body --------------
Function fn_792 = {FunctionType, -1, "rest_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_809}}};


// --------- str --------------
Function fn_810;

// --------- anon --------------
Function fn_812;
Value *arityImpl_813(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_153(empty_list, arg1);
Value *rslt3 = arityImpl_118(empty_list, arg0, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- anon main body --------------
Function fn_812 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_813}}};


// --------- anon --------------
Function fn_814;
Value *arityImpl_815(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = arityImpl_165(empty_list, val1, arg0);
incRef((Value *)&_num_13);
dec_and_free(rslt2);
return((Value *)&_num_13);
};

Value *arityImpl_811(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *cond1;
Value *rslt8 = arityImpl_138(empty_list, arg0);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef((Value *)&_str_56);
cond1 = (Value *)&_str_56;
} else {
dec_and_free(rslt8);
Value *rslt2 = arityImpl_692(empty_list, arg0, (Value *)&protoFn_276);
Value *rslt4 = arityImpl_685(empty_list, rslt2, (Value *)&_num_13, (Value *)&fn_812);
Value *rslt5 = arityImpl_162(empty_list, rslt4);
FnArity *arity_6 = malloc_fnArity();
arity_6->type = FnArityType;
arity_6->count = 1;
arity_6->closures = empty_list;
arity_6->variadic = 0;
arity_6->fn = arityImpl_815;
incRef((Value *)rslt5);
arity_6->closures = listCons((Value *)rslt5, (List *)arity_6->closures);
Function *fn_814 = malloc_function(1);
fn_814->type = FunctionType;
fn_814->name = "anon";
fn_814->arityCount = 1;
fn_814->arities[0] = arity_6;
Value *rslt7 = arityImpl_708(empty_list, rslt2, (Value *)fn_814);
incRef(rslt5);
cond1 = rslt5;
dec_and_free((Value *)fn_814);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt2);
}
return(cond1);
};

// --------- str main body --------------
Function fn_810 = {FunctionType, -1, "str", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_811}}};


// --------- take --------------
Function fn_817;
Value *arityImpl_818(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt9 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt9);
Value *rslt10 = arityImpl_442(empty_list, (Value *)&_num_13, arg1);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt10);
List *arg5 = (List *)arg0;
Value *arg3 = arg5->head;
if (arg5->tail) arg5->tail->len = arg5->len - 1;
arg5 = arg5->tail;
Value *arg4 = (Value *) arg5;
Value *rslt6 = arityImpl_743(empty_list, arg1);
Value *rslt7 = arityImpl_818(closures, arg4, rslt6);
Value *rslt8 = arityImpl_132(empty_list, arg3, rslt7);
incRef(rslt8);
cond2 = rslt8;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt7);
}
}
return(cond2);
};


// --------- take main body --------------
Function fn_817 = {FunctionType, -1, "take", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_818}}};


// --------- drop --------------
Function fn_820;
Value *arityImpl_821(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt6 = arityImpl_589(empty_list, arg1, (Value *)&_num_1);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt6);
Value *rslt3 = protoFnImpl_338(empty_list, arg0);
Value *rslt4 = arityImpl_743(empty_list, arg1);
Value *rslt5 = arityImpl_821(closures, rslt3, rslt4);
incRef(rslt5);
cond2 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- drop main body --------------
Function fn_820 = {FunctionType, -1, "drop", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_821}}};


// --------- split --------------
Function fn_823;
Value *arityImpl_824(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt9 = protoFnImpl_319(empty_list, arg0);
Value *rslt10 = arityImpl_589(empty_list, arg1, (Value *)&_num_1);
List *varArgs11 = empty_list;
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
incRef((Value *)rslt9);
varArgs11 = (List *)listCons((Value *)rslt9, varArgs11);
Value *rslt12 = arityImpl_438(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
dec_and_free(rslt10);
dec_and_free(rslt9);

if (isTrue(rslt12)) {
dec_and_free(rslt12);
Value *rslt13 = arityImpl_607(empty_list, arg2);
List *varArgs14 = empty_list;
incRef((Value *)arg0);
varArgs14 = (List *)listCons((Value *)arg0, varArgs14);
incRef((Value *)rslt13);
varArgs14 = (List *)listCons((Value *)rslt13, varArgs14);
Value *rslt15 = arityImpl_259(empty_list, (Value *)varArgs14);
dec_and_free((Value *)varArgs14);
incRef(rslt15);
cond3 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt13);
} else {
dec_and_free(rslt12);
Value *rslt4 = protoFnImpl_338(empty_list, arg0);
Value *rslt5 = arityImpl_743(empty_list, arg1);
Value *rslt6 = protoFnImpl_342(empty_list, arg0);
Value *rslt7 = arityImpl_132(empty_list, rslt6, arg2);
Value *rslt8 = arityImpl_824(closures, rslt4, rslt5, rslt7);
incRef(rslt8);
cond3 = rslt8;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
return(cond3);
};

Value *arityImpl_825(List *closures, Value *arg0, Value *arg1) {
Value *rslt5;
FnArity *arity2 = findFnArity((Value *)&fn_823, 3);
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
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)(Value *)&fn_823)->name);
  abort();
}
return(rslt5);
};


// --------- split main body --------------
Function fn_823 = {FunctionType, -1, "split", 2, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_824}, &(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_825}}};


// --------- replace-at-nth --------------
Function fn_827;
Value *arityImpl_828(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt14 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt14)) {
dec_and_free(rslt14);
incRef(arg0);
cond3 = arg0;
} else {
dec_and_free(rslt14);
Value *rslt15 = protoFnImpl_313(empty_list, arg0);
Value *rslt16 = arityImpl_743(empty_list, rslt15);
Value *rslt17 = arityImpl_589(empty_list, rslt16, arg1);
dec_and_free(rslt15);
dec_and_free(rslt16);

if (isTrue(rslt17)) {
dec_and_free(rslt17);
incRef(arg0);
cond3 = arg0;
} else {
dec_and_free(rslt17);
Value *rslt4 = arityImpl_825(empty_list, arg0, arg1);
List *arg7 = (List *)rslt4;
Value *arg5 = arg7->head;
if (arg7->tail) arg7->tail->len = arg7->len - 1;
arg7 = arg7->tail;
Value *arg6 = arg7->head;
if (arg7->tail) arg7->tail->len = arg7->len - 1;
arg7 = arg7->tail;
List *varArgs8 = empty_list;
incRef((Value *)arg2);
varArgs8 = (List *)listCons((Value *)arg2, varArgs8);
Value *rslt9 = arityImpl_259(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_338(empty_list, arg6);
List *varArgs11 = empty_list;
incRef((Value *)rslt10);
varArgs11 = (List *)listCons((Value *)rslt10, varArgs11);
incRef((Value *)rslt9);
varArgs11 = (List *)listCons((Value *)rslt9, varArgs11);
Value *rslt12 = arityImpl_259(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
Value *rslt13 = protoFnImpl_368(empty_list, arg5, rslt12);
incRef(rslt13);
cond3 = rslt13;
dec_and_free(rslt10);
dec_and_free(rslt13);
dec_and_free(rslt9);
dec_and_free(rslt12);
dec_and_free(rslt4);
}
}
return(cond3);
};


// --------- replace-at-nth main body --------------
Function fn_827 = {FunctionType, -1, "replace-at-nth", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_828}}};


// --------- remove-nth --------------
Function fn_830;
Value *arityImpl_831(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt11 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt11);
Value *rslt12 = protoFnImpl_313(empty_list, arg0);
Value *rslt13 = arityImpl_743(empty_list, rslt12);
Value *rslt14 = arityImpl_589(empty_list, rslt13, arg1);
dec_and_free(rslt13);
dec_and_free(rslt12);

if (isTrue(rslt14)) {
dec_and_free(rslt14);
incRef(arg0);
cond2 = arg0;
} else {
dec_and_free(rslt14);
Value *rslt3 = arityImpl_825(empty_list, arg0, arg1);
List *arg6 = (List *)rslt3;
Value *arg4 = arg6->head;
if (arg6->tail) arg6->tail->len = arg6->len - 1;
arg6 = arg6->tail;
Value *arg5 = arg6->head;
if (arg6->tail) arg6->tail->len = arg6->len - 1;
arg6 = arg6->tail;
Value *rslt7 = protoFnImpl_338(empty_list, arg5);
List *varArgs8 = empty_list;
incRef((Value *)rslt7);
varArgs8 = (List *)listCons((Value *)rslt7, varArgs8);
Value *rslt9 = arityImpl_259(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = protoFnImpl_368(empty_list, arg4, rslt9);
incRef(rslt10);
cond2 = rslt10;
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt7);
dec_and_free(rslt3);
}
}
return(cond2);
};


// --------- remove-nth main body --------------
Function fn_830 = {FunctionType, -1, "remove-nth", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_831}}};


// --------- partition --------------
Function fn_833;
Value *arityImpl_834(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = protoFnImpl_313(empty_list, arg0);
Value *rslt8 = arityImpl_589(empty_list, rslt7, arg1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt8);
Value *rslt3 = arityImpl_818(empty_list, arg0, arg1);
Value *rslt4 = arityImpl_821(empty_list, arg0, arg1);
Value *rslt5 = arityImpl_834(closures, rslt4, arg1);
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
Function fn_833 = {FunctionType, -1, "partition", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_834}}};


// --------- partition-all --------------
Function fn_836;
Value *arityImpl_837(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = protoFnImpl_313(empty_list, arg0);
Value *rslt8 = arityImpl_589(empty_list, rslt7, arg1);
dec_and_free(rslt7);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
List *varArgs9 = empty_list;
incRef((Value *)arg0);
varArgs9 = (List *)listCons((Value *)arg0, varArgs9);
Value *rslt10 = arityImpl_259(empty_list, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
incRef(rslt10);
cond2 = rslt10;
dec_and_free(rslt10);
} else {
dec_and_free(rslt8);
Value *rslt3 = arityImpl_818(empty_list, arg0, arg1);
Value *rslt4 = arityImpl_821(empty_list, arg0, arg1);
Value *rslt5 = arityImpl_837(closures, rslt4, arg1);
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
Function fn_836 = {FunctionType, -1, "partition-all", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_837}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[21];} _str_57 = {1, -1, 20,"'nth' from empty seq"};

// --------- nth --------------
Function fn_839;
Value *arityImpl_840(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
List *varArgs8 = empty_list;
incRef((Value *)(Value *)&_str_57);
varArgs8 = (List *)listCons((Value *)(Value *)&_str_57, varArgs8);
Value *rslt9 = arityImpl_728(empty_list, (Value *)varArgs8);
dec_and_free((Value *)varArgs8);
Value *rslt10 = arityImpl_96(empty_list);
incRef(rslt10);
cond2 = rslt10;
dec_and_free(rslt10);
dec_and_free(rslt9);
} else {
dec_and_free(rslt7);
Value *rslt11 = arityImpl_442(empty_list, arg1, (Value *)&_num_13);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
Value *rslt12 = protoFnImpl_340(empty_list, arg0);
Value *rslt13 = protoFnImpl_342(empty_list, rslt12);
incRef(rslt13);
cond2 = rslt13;
dec_and_free(rslt13);
dec_and_free(rslt12);
} else {
dec_and_free(rslt11);
Value *rslt3 = protoFnImpl_340(empty_list, arg0);
Value *rslt4 = protoFnImpl_338(empty_list, rslt3);
Value *rslt5 = arityImpl_743(empty_list, arg1);
Value *rslt6 = arityImpl_840(closures, rslt4, rslt5);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
}
return(cond2);
};

Value *arityImpl_841(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt8 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt8)) {
dec_and_free(rslt8);
incRef(arg2);
cond3 = arg2;
} else {
dec_and_free(rslt8);
Value *rslt9 = arityImpl_442(empty_list, arg1, (Value *)&_num_13);

if (isTrue(rslt9)) {
dec_and_free(rslt9);
Value *rslt10 = protoFnImpl_340(empty_list, arg0);
Value *rslt11 = protoFnImpl_342(empty_list, rslt10);
incRef(rslt11);
cond3 = rslt11;
dec_and_free(rslt10);
dec_and_free(rslt11);
} else {
dec_and_free(rslt9);
Value *rslt4 = protoFnImpl_340(empty_list, arg0);
Value *rslt5 = protoFnImpl_338(empty_list, rslt4);
Value *rslt6 = arityImpl_743(empty_list, arg1);
Value *rslt7 = arityImpl_841(closures, rslt5, rslt6, arg2);
incRef(rslt7);
cond3 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
}
return(cond3);
};


// --------- nth main body --------------
Function fn_839 = {FunctionType, -1, "nth", 2, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_840}, &(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_841}}};


// --------- last --------------
Function fn_843;
Value *arityImpl_844(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_313(empty_list, arg0);
Value *rslt3 = arityImpl_743(empty_list, rslt2);
Value *rslt4 = arityImpl_840(empty_list, arg0, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};


// --------- last main body --------------
Function fn_843 = {FunctionType, -1, "last", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_844}}};


// --------- butlast --------------
Function fn_846;
Value *arityImpl_847(List *closures, Value *arg0) {
Value *cond1;
Value *rslt6 = protoFnImpl_319(empty_list, arg0);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(arg0);
cond1 = arg0;
} else {
dec_and_free(rslt6);
Value *rslt2 = protoFnImpl_313(empty_list, arg0);
Value *rslt3 = arityImpl_743(empty_list, rslt2);
Value *rslt4 = arityImpl_825(empty_list, arg0, rslt3);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
incRef(rslt5);
cond1 = rslt5;
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
}
return(cond1);
};


// --------- butlast main body --------------
Function fn_846 = {FunctionType, -1, "butlast", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_847}}};


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
Value *var_849 = (Value *)&emptyBMI;
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[3];} _str_58 = {1, -1, 2,"{}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_60 = {1, -1, 1,"}"};
struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_59 = {1, -1, 1,"{"};

// --------- count_impl --------------
Function fn_850;
Value *arityImpl_863(List *closures, Value *arg0) {

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
Function fn_850 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_863}}};


// --------- empty?_impl --------------
Function fn_851;
Value *arityImpl_864(List *closures, Value *arg0) {

if (((BitmapIndexedNode *)arg0)->bitmap == 0)
   return(true);
else
   return(false);
};


// --------- empty?_impl main body --------------
Function fn_851 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_864}}};


// --------- zero_impl --------------
Function fn_852;
Value *arityImpl_865(List *closures, Value *arg0) {
incRef(var_849);
return(var_849);
};


// --------- zero_impl main body --------------
Function fn_852 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_865}}};


// --------- comp*_impl --------------
Function fn_853;

// --------- anon --------------
Function fn_867;

// --------- anon --------------
Function fn_869;
Value *arityImpl_870(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_616(empty_list, (Value *)&protoFn_399, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_869 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_870}}};

Value *arityImpl_868(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_340(empty_list, arg1);
Value *rslt4 = protoFnImpl_321(empty_list, rslt2, arg0, (Value *)&fn_869);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt4);
};


// --------- anon main body --------------
Function fn_867 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_868}}};

Value *arityImpl_866(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_867);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_853 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_866}}};


// --------- get_impl --------------
Function fn_854;
Value *arityImpl_871(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_854 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_871}}};


// --------- keys_impl --------------
Function fn_855;
Value *arityImpl_872(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_267(empty_list, rslt1, (Value *)&protoFn_330);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keys_impl main body --------------
Function fn_855 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_872}}};


// --------- vals_impl --------------
Function fn_856;
Value *arityImpl_873(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_267(empty_list, rslt1, (Value *)&fn_349);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- vals_impl main body --------------
Function fn_856 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_873}}};


// --------- assoc_impl --------------
Function fn_857;
Value *arityImpl_874(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_857 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_874}}};


// --------- string-list_impl --------------
Function fn_858;

// --------- anon --------------
Function fn_876;
Value *arityImpl_877(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_267(empty_list, arg0, (Value *)&protoFn_276);
List *varArgs2 = empty_list;
incRef((Value *)(Value *)&_str_53);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_53, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_711(empty_list, rslt1, rslt3);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_368(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- anon main body --------------
Function fn_876 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_877}}};

Value *arityImpl_875(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *cond2;
Value *rslt18 = arityImpl_138(empty_list, rslt1);

if (isTrue(rslt18)) {
dec_and_free(rslt18);
List *varArgs19 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs19 = (List *)listCons((Value *)(Value *)&_str_58, varArgs19);
Value *rslt20 = arityImpl_259(empty_list, (Value *)varArgs19);
dec_and_free((Value *)varArgs19);
incRef(rslt20);
cond2 = rslt20;
dec_and_free(rslt20);
} else {
dec_and_free(rslt18);
Value *rslt4 = protoFnImpl_267(empty_list, rslt1, (Value *)&fn_876);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_51);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_51, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = arityImpl_711(empty_list, rslt4, rslt6);
Value *rslt8 = arityImpl_141(empty_list, rslt7);
Value *rslt9 = arityImpl_144(empty_list, rslt7);
Value *rslt10 = protoFnImpl_368(empty_list, rslt8, rslt9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_59, varArgs11);
Value *rslt12 = arityImpl_259(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)(Value *)&_str_60);
varArgs13 = (List *)listCons((Value *)(Value *)&_str_60, varArgs13);
Value *rslt14 = arityImpl_259(empty_list, (Value *)varArgs13);
dec_and_free((Value *)varArgs13);
List *varArgs15 = empty_list;
incRef((Value *)rslt14);
varArgs15 = (List *)listCons((Value *)rslt14, varArgs15);
incRef((Value *)rslt10);
varArgs15 = (List *)listCons((Value *)rslt10, varArgs15);
Value *rslt16 = arityImpl_259(empty_list, (Value *)varArgs15);
dec_and_free((Value *)varArgs15);
Value *rslt17 = arityImpl_698(empty_list, rslt12, rslt16);
incRef(rslt17);
cond2 = rslt17;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt14);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt12);
dec_and_free(rslt17);
dec_and_free(rslt16);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};


// --------- string-list_impl main body --------------
Function fn_858 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_875}}};


// --------- seq_impl --------------
Function fn_859;
Value *arityImpl_878(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_396(empty_list, arg0, var_129);
return(rslt1);
};


// --------- seq_impl main body --------------
Function fn_859 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_878}}};


// --------- hash-seq_impl --------------
Function fn_860;
Value *arityImpl_879(List *closures, Value *arg0, Value *arg1) {

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
Function fn_860 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_879}}};


// --------- assoc*_impl --------------
Function fn_861;
Value *arityImpl_880(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_861 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_880}}};


// --------- get*_impl --------------
Function fn_862;
Value *arityImpl_881(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_862 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_881}}};


// --------- count_impl --------------
Function fn_882;
Value *arityImpl_895(List *closures, Value *arg0) {

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
Function fn_882 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_895}}};


// --------- empty?_impl --------------
Function fn_883;
Value *arityImpl_896(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};


// --------- empty?_impl main body --------------
Function fn_883 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_896}}};


// --------- zero_impl --------------
Function fn_884;
Value *arityImpl_897(List *closures, Value *arg0) {
incRef(var_849);
return(var_849);
};


// --------- zero_impl main body --------------
Function fn_884 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_897}}};


// --------- comp*_impl --------------
Function fn_885;

// --------- anon --------------
Function fn_899;

// --------- anon --------------
Function fn_901;
Value *arityImpl_902(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_616(empty_list, (Value *)&protoFn_399, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_901 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_902}}};

Value *arityImpl_900(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_340(empty_list, arg1);
Value *rslt4 = protoFnImpl_321(empty_list, rslt2, arg0, (Value *)&fn_901);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt4);
};


// --------- anon main body --------------
Function fn_899 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_900}}};

Value *arityImpl_898(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_899);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_885 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_898}}};


// --------- get_impl --------------
Function fn_886;
Value *arityImpl_903(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_886 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_903}}};


// --------- keys_impl --------------
Function fn_887;
Value *arityImpl_904(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_267(empty_list, rslt1, (Value *)&protoFn_330);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keys_impl main body --------------
Function fn_887 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_904}}};


// --------- vals_impl --------------
Function fn_888;
Value *arityImpl_905(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_267(empty_list, rslt1, (Value *)&fn_349);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- vals_impl main body --------------
Function fn_888 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_905}}};


// --------- assoc_impl --------------
Function fn_889;
Value *arityImpl_906(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_889 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_906}}};


// --------- string-list_impl --------------
Function fn_890;

// --------- anon --------------
Function fn_908;
Value *arityImpl_909(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_267(empty_list, arg0, (Value *)&protoFn_276);
List *varArgs2 = empty_list;
incRef((Value *)(Value *)&_str_53);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_53, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_711(empty_list, rslt1, rslt3);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_368(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- anon main body --------------
Function fn_908 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_909}}};

Value *arityImpl_907(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *cond2;
Value *rslt18 = arityImpl_138(empty_list, rslt1);

if (isTrue(rslt18)) {
dec_and_free(rslt18);
List *varArgs19 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs19 = (List *)listCons((Value *)(Value *)&_str_58, varArgs19);
Value *rslt20 = arityImpl_259(empty_list, (Value *)varArgs19);
dec_and_free((Value *)varArgs19);
incRef(rslt20);
cond2 = rslt20;
dec_and_free(rslt20);
} else {
dec_and_free(rslt18);
Value *rslt4 = protoFnImpl_267(empty_list, rslt1, (Value *)&fn_908);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_51);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_51, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = arityImpl_711(empty_list, rslt4, rslt6);
Value *rslt8 = arityImpl_141(empty_list, rslt7);
Value *rslt9 = arityImpl_144(empty_list, rslt7);
Value *rslt10 = protoFnImpl_368(empty_list, rslt8, rslt9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_59, varArgs11);
Value *rslt12 = arityImpl_259(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)(Value *)&_str_60);
varArgs13 = (List *)listCons((Value *)(Value *)&_str_60, varArgs13);
Value *rslt14 = arityImpl_259(empty_list, (Value *)varArgs13);
dec_and_free((Value *)varArgs13);
List *varArgs15 = empty_list;
incRef((Value *)rslt14);
varArgs15 = (List *)listCons((Value *)rslt14, varArgs15);
incRef((Value *)rslt10);
varArgs15 = (List *)listCons((Value *)rslt10, varArgs15);
Value *rslt16 = arityImpl_259(empty_list, (Value *)varArgs15);
dec_and_free((Value *)varArgs15);
Value *rslt17 = arityImpl_698(empty_list, rslt12, rslt16);
incRef(rslt17);
cond2 = rslt17;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt14);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt12);
dec_and_free(rslt17);
dec_and_free(rslt16);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};


// --------- string-list_impl main body --------------
Function fn_890 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_907}}};


// --------- seq_impl --------------
Function fn_891;
Value *arityImpl_910(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_396(empty_list, arg0, var_129);
return(rslt1);
};


// --------- seq_impl main body --------------
Function fn_891 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_910}}};


// --------- hash-seq_impl --------------
Function fn_892;
Value *arityImpl_911(List *closures, Value *arg0, Value *arg1) {

ArrayNode *node = (ArrayNode *)arg0;
List *seq = (List *)arg1;
for (int i = 0; i < 32; i++) {
   if (node->array[i] != (Value *)0)
     seq = (List *)hashSeq(node->array[i], (Value *)seq);
}
return((Value *)seq);
};


// --------- hash-seq_impl main body --------------
Function fn_892 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_911}}};


// --------- assoc*_impl --------------
Function fn_893;
Value *arityImpl_912(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_893 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_912}}};


// --------- get*_impl --------------
Function fn_894;
Value *arityImpl_913(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_894 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_913}}};


// --------- count_impl --------------
Function fn_914;
Value *arityImpl_927(List *closures, Value *arg0) {

return(numberValue(((HashCollisionNode *) arg0)->count / 2));
};


// --------- count_impl main body --------------
Function fn_914 = {FunctionType, -1, "count_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_927}}};


// --------- empty?_impl --------------
Function fn_915;
Value *arityImpl_928(List *closures, Value *arg0) {
incRef(var_76);
return(var_76);
};


// --------- empty?_impl main body --------------
Function fn_915 = {FunctionType, -1, "empty?_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_928}}};


// --------- zero_impl --------------
Function fn_916;
Value *arityImpl_929(List *closures, Value *arg0) {
incRef(var_849);
return(var_849);
};


// --------- zero_impl main body --------------
Function fn_916 = {FunctionType, -1, "zero_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_929}}};


// --------- comp*_impl --------------
Function fn_917;

// --------- anon --------------
Function fn_931;

// --------- anon --------------
Function fn_933;
Value *arityImpl_934(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_616(empty_list, (Value *)&protoFn_399, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_933 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_934}}};

Value *arityImpl_932(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_340(empty_list, arg1);
Value *rslt4 = protoFnImpl_321(empty_list, rslt2, arg0, (Value *)&fn_933);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt2);
return(rslt4);
};


// --------- anon main body --------------
Function fn_931 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_932}}};

Value *arityImpl_930(List *closures, Value *arg0, Value *arg1) {
Value *rslt3 = protoFnImpl_321(empty_list, arg1, arg0, (Value *)&fn_931);
return(rslt3);
};


// --------- comp*_impl main body --------------
Function fn_917 = {FunctionType, -1, "comp*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_930}}};


// --------- get_impl --------------
Function fn_918;
Value *arityImpl_935(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *found = get(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(found);
};


// --------- get_impl main body --------------
Function fn_918 = {FunctionType, -1, "get_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_935}}};


// --------- keys_impl --------------
Function fn_919;
Value *arityImpl_936(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_267(empty_list, rslt1, (Value *)&protoFn_330);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- keys_impl main body --------------
Function fn_919 = {FunctionType, -1, "keys_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_936}}};


// --------- vals_impl --------------
Function fn_920;
Value *arityImpl_937(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *rslt2 = protoFnImpl_267(empty_list, rslt1, (Value *)&fn_349);
incRef(rslt2);
dec_and_free(rslt1);
dec_and_free(rslt2);
return(rslt2);
};


// --------- vals_impl main body --------------
Function fn_920 = {FunctionType, -1, "vals_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_937}}};


// --------- assoc_impl --------------
Function fn_921;
Value *arityImpl_938(List *closures, Value *arg0, Value *arg1, Value *arg2) {

Value *hash = sha1(arg1);
Value *shift = numberValue(0);
Value *newNode = assoc(arg0, arg1, arg2, hash, shift);
dec_and_free(shift);
dec_and_free(hash);
return(newNode);
};


// --------- assoc_impl main body --------------
Function fn_921 = {FunctionType, -1, "assoc_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_938}}};


// --------- string-list_impl --------------
Function fn_922;

// --------- anon --------------
Function fn_940;
Value *arityImpl_941(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_267(empty_list, arg0, (Value *)&protoFn_276);
List *varArgs2 = empty_list;
incRef((Value *)(Value *)&_str_53);
varArgs2 = (List *)listCons((Value *)(Value *)&_str_53, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_711(empty_list, rslt1, rslt3);
Value *rslt5 = arityImpl_141(empty_list, rslt4);
Value *rslt6 = arityImpl_144(empty_list, rslt4);
Value *rslt7 = protoFnImpl_368(empty_list, rslt5, rslt6);
incRef(rslt7);
dec_and_free(rslt6);
dec_and_free(rslt1);
dec_and_free(rslt5);
dec_and_free(rslt4);
dec_and_free(rslt7);
dec_and_free(rslt3);
return(rslt7);
};


// --------- anon main body --------------
Function fn_940 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_941}}};

Value *arityImpl_939(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_340(empty_list, arg0);
Value *cond2;
Value *rslt18 = arityImpl_138(empty_list, rslt1);

if (isTrue(rslt18)) {
dec_and_free(rslt18);
List *varArgs19 = empty_list;
incRef((Value *)(Value *)&_str_58);
varArgs19 = (List *)listCons((Value *)(Value *)&_str_58, varArgs19);
Value *rslt20 = arityImpl_259(empty_list, (Value *)varArgs19);
dec_and_free((Value *)varArgs19);
incRef(rslt20);
cond2 = rslt20;
dec_and_free(rslt20);
} else {
dec_and_free(rslt18);
Value *rslt4 = protoFnImpl_267(empty_list, rslt1, (Value *)&fn_940);
List *varArgs5 = empty_list;
incRef((Value *)(Value *)&_str_51);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_51, varArgs5);
Value *rslt6 = arityImpl_259(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = arityImpl_711(empty_list, rslt4, rslt6);
Value *rslt8 = arityImpl_141(empty_list, rslt7);
Value *rslt9 = arityImpl_144(empty_list, rslt7);
Value *rslt10 = protoFnImpl_368(empty_list, rslt8, rslt9);
List *varArgs11 = empty_list;
incRef((Value *)(Value *)&_str_59);
varArgs11 = (List *)listCons((Value *)(Value *)&_str_59, varArgs11);
Value *rslt12 = arityImpl_259(empty_list, (Value *)varArgs11);
dec_and_free((Value *)varArgs11);
List *varArgs13 = empty_list;
incRef((Value *)(Value *)&_str_60);
varArgs13 = (List *)listCons((Value *)(Value *)&_str_60, varArgs13);
Value *rslt14 = arityImpl_259(empty_list, (Value *)varArgs13);
dec_and_free((Value *)varArgs13);
List *varArgs15 = empty_list;
incRef((Value *)rslt14);
varArgs15 = (List *)listCons((Value *)rslt14, varArgs15);
incRef((Value *)rslt10);
varArgs15 = (List *)listCons((Value *)rslt10, varArgs15);
Value *rslt16 = arityImpl_259(empty_list, (Value *)varArgs15);
dec_and_free((Value *)varArgs15);
Value *rslt17 = arityImpl_698(empty_list, rslt12, rslt16);
incRef(rslt17);
cond2 = rslt17;
dec_and_free(rslt6);
dec_and_free(rslt8);
dec_and_free(rslt14);
dec_and_free(rslt10);
dec_and_free(rslt9);
dec_and_free(rslt12);
dec_and_free(rslt17);
dec_and_free(rslt16);
dec_and_free(rslt4);
dec_and_free(rslt7);
}
incRef(cond2);
dec_and_free(rslt1);
dec_and_free(cond2);
return(cond2);
};


// --------- string-list_impl main body --------------
Function fn_922 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_939}}};


// --------- seq_impl --------------
Function fn_923;
Value *arityImpl_942(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_396(empty_list, arg0, var_129);
return(rslt1);
};


// --------- seq_impl main body --------------
Function fn_923 = {FunctionType, -1, "seq_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_942}}};


// --------- hash-seq_impl --------------
Function fn_924;
Value *arityImpl_943(List *closures, Value *arg0, Value *arg1) {

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
Function fn_924 = {FunctionType, -1, "hash-seq_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_943}}};


// --------- assoc*_impl --------------
Function fn_925;
Value *arityImpl_944(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_925 = {FunctionType, -1, "assoc*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_944}}};


// --------- get*_impl --------------
Function fn_926;
Value *arityImpl_945(List *closures, Value *arg0, Value *arg1, Value *arg2, Value *arg3, Value *arg4) {

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
Function fn_926 = {FunctionType, -1, "get*_impl", 1, {&(FnArity){FnArityType, -1, 5, (List *)0, 0, arityImpl_945}}};


// --------- hash-map --------------
Function fn_946;

// --------- anon --------------
Function fn_948;
Value *arityImpl_949(List *closures, Value *arg0, Value *arg1) {
List *varArgs2 = empty_list;
incRef((Value *)arg1);
varArgs2 = (List *)listCons((Value *)arg1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_616(empty_list, (Value *)&protoFn_399, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- anon main body --------------
Function fn_948 = {FunctionType, -1, "anon", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_949}}};

Value *arityImpl_947(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = (Value *) argsList;
Value *rslt1 = arityImpl_834(empty_list, arg0, (Value *)&_num_2);
Value *rslt3 = protoFnImpl_321(empty_list, rslt1, var_849, (Value *)&fn_948);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};

// --------- hash-map main body --------------
Function fn_946 = {FunctionType, -1, "hash-map", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_947}}};


// --------- =*_impl --------------
Function fn_952;
Value *arityImpl_953(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_99(empty_list, arg0);
Value *rslt3 = arityImpl_99(empty_list, arg1);
Value *rslt4 = arityImpl_442(empty_list, rslt2, rslt3);
incRef(rslt4);
dec_and_free(rslt4);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt4);
};


// --------- =*_impl main body --------------
Function fn_952 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_953}}};

Value *protoImpl_954(List *closures, Value *arg0, Value *arg1) {
FnArity *arityPtr = ((Function *)((ReifiedVal *)arg0)->impls[0])->arities[0];
Value *rval = ((FnType2 *)arityPtr->fn)(arityPtr->closures, arg0, arg1);
return(rval);
};

Function protoFn_951 = {FunctionType, -1, "=*", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, protoImpl_954}}};

ReifiedVal reified_955 = {17, -1, 1, {(Value *)&fn_952}};

// --------- merge-with --------------
Function fn_957;

// --------- anon --------------
Function fn_959;

// --------- anon --------------
Function fn_961;
Value *arityImpl_962(List *closures, Value *arg0, Value *arg3) {
Value * val7  = closures->head;
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
Value *rslt5 = protoFnImpl_420(empty_list, arg0, arg1, (Value *)&reified_955);
Value *cond6;
Value *rslt13 = arityImpl_442(empty_list, (Value *)&reified_955, rslt5);

if (isTrue(rslt13)) {
dec_and_free(rslt13);
Value *rslt14 = protoFnImpl_413(empty_list, arg0, arg1, arg2);
incRef(rslt14);
cond6 = rslt14;
dec_and_free(rslt14);
} else {
dec_and_free(rslt13);
Value *rslt11;
if((val7)->type != FunctionType) {
rslt11 = protoFnImpl_13(empty_list, val7, rslt5, arg2);
} else {
FnArity *arity8 = findFnArity(val7, 2);
if(arity8 != (FnArity *)0 && !arity8->variadic) {
FnType2 *fn10 = (FnType2 *)arity8->fn;
rslt11 = fn10(arity8->closures, rslt5, arg2);
} else if(arity8 != (FnArity *)0 && arity8->variadic) {
FnType1 *fn10 = (FnType1 *)arity8->fn;
List *varArgs9 = empty_list;
incRef(arg2);
varArgs9 = (List *)listCons(arg2, varArgs9);
incRef(rslt5);
varArgs9 = (List *)listCons(rslt5, varArgs9);
rslt11 = fn10(arity8->closures, (Value *)varArgs9);
dec_and_free((Value *)varArgs9);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)val7)->name);
  abort();
}
}
Value *rslt12 = protoFnImpl_413(empty_list, arg0, arg1, rslt11);
incRef(rslt12);
cond6 = rslt12;
dec_and_free(rslt11);
dec_and_free(rslt12);
}
incRef(cond6);
dec_and_free(cond6);
dec_and_free(rslt5);
return(cond6);
};

Value *arityImpl_960(List *closures, Value *arg0, Value *arg1) {
Value * val4  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
Value *rslt2 = protoFnImpl_340(empty_list, arg1);
FnArity *arity_3 = malloc_fnArity();
arity_3->type = FnArityType;
arity_3->count = 2;
arity_3->closures = empty_list;
arity_3->variadic = 0;
arity_3->fn = arityImpl_962;
incRef((Value *)val4);
arity_3->closures = listCons((Value *)val4, (List *)arity_3->closures);
Function *fn_961 = malloc_function(1);
fn_961->type = FunctionType;
fn_961->name = "anon";
fn_961->arityCount = 1;
fn_961->arities[0] = arity_3;
Value *rslt5 = protoFnImpl_321(empty_list, rslt2, arg0, (Value *)fn_961);
incRef(rslt5);
dec_and_free((Value *)fn_961);
dec_and_free(rslt5);
dec_and_free(rslt2);
return(rslt5);
};

Value *arityImpl_958(List *closures, Value *varArgs) {
List *argsList = (List *)varArgs;
Value *arg0 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg1 = argsList->head;
if (argsList->tail) argsList->tail->len = argsList->len - 1;
argsList = argsList->tail;
Value *arg2 = (Value *) argsList;
Value *cond3;
Value *rslt6 = arityImpl_138(empty_list, arg2);

if (isTrue(rslt6)) {
dec_and_free(rslt6);
incRef(arg1);
cond3 = arg1;
} else {
dec_and_free(rslt6);
FnArity *arity_4 = malloc_fnArity();
arity_4->type = FnArityType;
arity_4->count = 2;
arity_4->closures = empty_list;
arity_4->variadic = 0;
arity_4->fn = arityImpl_960;
incRef((Value *)arg0);
arity_4->closures = listCons((Value *)arg0, (List *)arity_4->closures);
Function *fn_959 = malloc_function(1);
fn_959->type = FunctionType;
fn_959->name = "anon";
fn_959->arityCount = 1;
fn_959->arities[0] = arity_4;
Value *rslt5 = arityImpl_685(empty_list, arg2, arg1, (Value *)fn_959);
incRef(rslt5);
cond3 = rslt5;
dec_and_free((Value *)fn_959);
dec_and_free(rslt5);
}
return(cond3);
};

// --------- merge-with main body --------------
Function fn_957 = {FunctionType, -1, "merge-with", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 1, arityImpl_958}}};

SubString _kw_2 = {5, -1, 17, 0, 0, ":get-in-not-found"};

// --------- get-in --------------
Function fn_964;
Value *arityImpl_965(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt11 = protoFnImpl_313(empty_list, arg1);
Value *rslt12 = arityImpl_442(empty_list, rslt11, (Value *)&_num_13);
dec_and_free(rslt11);

if (isTrue(rslt12)) {
dec_and_free(rslt12);
incRef(arg2);
cond3 = arg2;
} else {
dec_and_free(rslt12);
Value *rslt13 = protoFnImpl_313(empty_list, arg1);
Value *rslt14 = arityImpl_442(empty_list, rslt13, (Value *)&_num_1);
dec_and_free(rslt13);

if (isTrue(rslt14)) {
dec_and_free(rslt14);
Value *rslt15 = protoFnImpl_342(empty_list, arg1);
Value *rslt16 = protoFnImpl_420(empty_list, arg0, rslt15, arg2);
incRef(rslt16);
cond3 = rslt16;
dec_and_free(rslt15);
dec_and_free(rslt16);
} else {
dec_and_free(rslt14);
List *arg6 = (List *)arg1;
Value *arg4 = arg6->head;
if (arg6->tail) arg6->tail->len = arg6->len - 1;
arg6 = arg6->tail;
Value *arg5 = (Value *) arg6;
Value *rslt7 = protoFnImpl_420(empty_list, arg0, arg4, (Value *)&_kw_2);
Value *cond8;
Value *rslt10 = arityImpl_442(empty_list, (Value *)&_kw_2, rslt7);

if (isTrue(rslt10)) {
dec_and_free(rslt10);
incRef(arg2);
cond8 = arg2;
} else {
dec_and_free(rslt10);
Value *rslt9 = arityImpl_965(closures, rslt7, arg5, arg2);
incRef(rslt9);
cond8 = rslt9;
dec_and_free(rslt9);
}
incRef(cond8);
cond3 = cond8;
dec_and_free(cond8);
dec_and_free(rslt7);
}
}
return(cond3);
};


// --------- get-in main body --------------
Function fn_964 = {FunctionType, -1, "get-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_965}}};

SubString _kw_3 = {5, -1, 14, 0, 0, ":update-in-nil"};

// --------- update-in --------------
Function fn_967;
Value *arityImpl_968(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt12 = protoFnImpl_313(empty_list, arg1);
Value *rslt13 = arityImpl_442(empty_list, rslt12, (Value *)&_num_13);
dec_and_free(rslt12);

if (isTrue(rslt13)) {
dec_and_free(rslt13);
incRef(arg0);
cond3 = arg0;
} else {
dec_and_free(rslt13);
Value *rslt14 = protoFnImpl_313(empty_list, arg1);
Value *rslt15 = arityImpl_442(empty_list, rslt14, (Value *)&_num_1);
dec_and_free(rslt14);

if (isTrue(rslt15)) {
dec_and_free(rslt15);
Value *rslt16 = protoFnImpl_342(empty_list, arg1);
Value *rslt17 = protoFnImpl_420(empty_list, arg0, rslt16, (Value *)&_kw_3);
Value *cond18;
Value *rslt24 = arityImpl_442(empty_list, (Value *)&_kw_3, rslt17);

if (isTrue(rslt24)) {
dec_and_free(rslt24);
incRef(arg0);
cond18 = arg0;
} else {
dec_and_free(rslt24);
Value *rslt22;
if((arg2)->type != FunctionType) {
rslt22 = protoFnImpl_11(empty_list, arg2, rslt17);
} else {
FnArity *arity19 = findFnArity(arg2, 1);
if(arity19 != (FnArity *)0 && !arity19->variadic) {
FnType1 *fn21 = (FnType1 *)arity19->fn;
rslt22 = fn21(arity19->closures, rslt17);
} else if(arity19 != (FnArity *)0 && arity19->variadic) {
FnType1 *fn21 = (FnType1 *)arity19->fn;
List *varArgs20 = empty_list;
incRef(rslt17);
varArgs20 = (List *)listCons(rslt17, varArgs20);
rslt22 = fn21(arity19->closures, (Value *)varArgs20);
dec_and_free((Value *)varArgs20);
} else {
fprintf(stderr, "\n*** no arity found for '%s'.\n", ((Function *)arg2)->name);
  abort();
}
}
Value *rslt23 = protoFnImpl_413(empty_list, arg0, rslt16, rslt22);
incRef(rslt23);
cond18 = rslt23;
dec_and_free(rslt22);
dec_and_free(rslt23);
}
incRef(cond18);
cond3 = cond18;
dec_and_free(cond18);
dec_and_free(rslt17);
dec_and_free(rslt16);
} else {
dec_and_free(rslt15);
List *arg6 = (List *)arg1;
Value *arg4 = arg6->head;
if (arg6->tail) arg6->tail->len = arg6->len - 1;
arg6 = arg6->tail;
Value *arg5 = (Value *) arg6;
Value *rslt7 = protoFnImpl_420(empty_list, arg0, arg4, (Value *)&_kw_3);
Value *cond8;
Value *rslt11 = arityImpl_442(empty_list, (Value *)&_kw_3, rslt7);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
incRef(arg0);
cond8 = arg0;
} else {
dec_and_free(rslt11);
Value *rslt9 = arityImpl_968(closures, rslt7, arg5, arg2);
Value *rslt10 = protoFnImpl_413(empty_list, arg0, arg4, rslt9);
incRef(rslt10);
cond8 = rslt10;
dec_and_free(rslt10);
dec_and_free(rslt9);
}
incRef(cond8);
cond3 = cond8;
dec_and_free(cond8);
dec_and_free(rslt7);
}
}
return(cond3);
};


// --------- update-in main body --------------
Function fn_967 = {FunctionType, -1, "update-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_968}}};

SubString _kw_4 = {5, -1, 13, 0, 0, ":assoc-in-nil"};

// --------- assoc-in --------------
Function fn_970;
Value *arityImpl_971(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *cond3;
Value *rslt16 = protoFnImpl_313(empty_list, arg1);
Value *rslt17 = arityImpl_442(empty_list, rslt16, (Value *)&_num_13);
dec_and_free(rslt16);

if (isTrue(rslt17)) {
dec_and_free(rslt17);
incRef(arg0);
cond3 = arg0;
} else {
dec_and_free(rslt17);
Value *rslt18 = protoFnImpl_313(empty_list, arg1);
Value *rslt19 = arityImpl_442(empty_list, rslt18, (Value *)&_num_1);
dec_and_free(rslt18);

if (isTrue(rslt19)) {
dec_and_free(rslt19);
Value *rslt20 = protoFnImpl_342(empty_list, arg1);
Value *rslt21 = protoFnImpl_413(empty_list, arg0, rslt20, arg2);
incRef(rslt21);
cond3 = rslt21;
dec_and_free(rslt20);
dec_and_free(rslt21);
} else {
dec_and_free(rslt19);
List *arg6 = (List *)arg1;
Value *arg4 = arg6->head;
if (arg6->tail) arg6->tail->len = arg6->len - 1;
arg6 = arg6->tail;
Value *arg5 = (Value *) arg6;
Value *rslt7 = protoFnImpl_420(empty_list, arg0, arg4, (Value *)&_kw_4);
Value *cond8;
Value *rslt11 = arityImpl_442(empty_list, (Value *)&_kw_4, rslt7);

if (isTrue(rslt11)) {
dec_and_free(rslt11);
List *varArgs12 = empty_list;
Value *rslt13 = arityImpl_947(empty_list, (Value *)varArgs12);
dec_and_free((Value *)varArgs12);
Value *rslt14 = arityImpl_971(closures, rslt13, arg5, arg2);
Value *rslt15 = protoFnImpl_413(empty_list, arg0, arg4, rslt14);
incRef(rslt15);
cond8 = rslt15;
dec_and_free(rslt15);
dec_and_free(rslt14);
dec_and_free(rslt13);
} else {
dec_and_free(rslt11);
Value *rslt9 = arityImpl_971(closures, rslt7, arg5, arg2);
Value *rslt10 = protoFnImpl_413(empty_list, arg0, arg4, rslt9);
incRef(rslt10);
cond8 = rslt10;
dec_and_free(rslt10);
dec_and_free(rslt9);
}
incRef(cond8);
cond3 = cond8;
dec_and_free(cond8);
dec_and_free(rslt7);
}
}
return(cond3);
};


// --------- assoc-in main body --------------
Function fn_970 = {FunctionType, -1, "assoc-in", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_971}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[19];} _str_61 = {1, -1, 18,"Could not look up "};

// --------- sha1_impl --------------
Function fn_973;
Value *arityImpl_978(List *closures, Value *arg0) {

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
Function fn_973 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_978}}};


// --------- =*_impl --------------
Function fn_974;
Value *arityImpl_979(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_159(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_974 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_979}}};


// --------- string-list_impl --------------
Function fn_975;
Value *arityImpl_980(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_273(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_975 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_980}}};


// --------- invoke_impl --------------
Function fn_976;
Value *arityImpl_981(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_420(empty_list, arg1, arg0, (Value *)&reified_955);
Value *cond3;
Value *rslt4 = arityImpl_442(empty_list, (Value *)&reified_955, rslt2);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)arg0);
varArgs5 = (List *)listCons((Value *)arg0, varArgs5);
incRef((Value *)(Value *)&_str_61);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_61, varArgs5);
Value *rslt6 = arityImpl_728(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = arityImpl_96(empty_list);
incRef(rslt7);
cond3 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
} else {
dec_and_free(rslt4);
incRef(rslt2);
cond3 = rslt2;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- invoke_impl main body --------------
Function fn_976 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_981}}};


// --------- name_impl --------------
Function fn_977;
Value *arityImpl_982(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_84(empty_list, arg0);
return(rslt1);
};


// --------- name_impl main body --------------
Function fn_977 = {FunctionType, -1, "name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_982}}};


// --------- sha1_impl --------------
Function fn_983;
Value *arityImpl_989(List *closures, Value *arg0) {

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
Function fn_983 = {FunctionType, -1, "sha1_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_989}}};


// --------- =*_impl --------------
Function fn_984;
Value *arityImpl_990(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = arityImpl_159(empty_list, arg0, arg1);
return(rslt2);
};


// --------- =*_impl main body --------------
Function fn_984 = {FunctionType, -1, "=*_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_990}}};


// --------- string-list_impl --------------
Function fn_985;
Value *arityImpl_991(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_273(empty_list, arg0);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
Value *rslt3 = arityImpl_259(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
return(rslt3);
};


// --------- string-list_impl main body --------------
Function fn_985 = {FunctionType, -1, "string-list_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_991}}};


// --------- invoke_impl --------------
Function fn_986;
Value *arityImpl_992(List *closures, Value *arg0, Value *arg1) {
Value *rslt2 = protoFnImpl_420(empty_list, arg1, arg0, (Value *)&reified_955);
Value *cond3;
Value *rslt4 = arityImpl_442(empty_list, (Value *)&reified_955, rslt2);

if (isTrue(rslt4)) {
dec_and_free(rslt4);
List *varArgs5 = empty_list;
incRef((Value *)arg0);
varArgs5 = (List *)listCons((Value *)arg0, varArgs5);
incRef((Value *)(Value *)&_str_61);
varArgs5 = (List *)listCons((Value *)(Value *)&_str_61, varArgs5);
Value *rslt6 = arityImpl_728(empty_list, (Value *)varArgs5);
dec_and_free((Value *)varArgs5);
Value *rslt7 = arityImpl_96(empty_list);
incRef(rslt7);
cond3 = rslt7;
dec_and_free(rslt6);
dec_and_free(rslt7);
} else {
dec_and_free(rslt4);
incRef(rslt2);
cond3 = rslt2;
}
incRef(cond3);
dec_and_free(cond3);
dec_and_free(rslt2);
return(cond3);
};


// --------- invoke_impl main body --------------
Function fn_986 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_992}}};


// --------- invoke_impl --------------
Function fn_987;
Value *arityImpl_993(List *closures, Value *arg0, Value *arg1, Value *arg2) {
Value *rslt3 = protoFnImpl_420(empty_list, arg1, arg0, arg2);
return(rslt3);
};


// --------- invoke_impl main body --------------
Function fn_987 = {FunctionType, -1, "invoke_impl", 1, {&(FnArity){FnArityType, -1, 3, (List *)0, 0, arityImpl_993}}};


// --------- name_impl --------------
Function fn_988;
Value *arityImpl_994(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_84(empty_list, arg0);
return(rslt1);
};


// --------- name_impl main body --------------
Function fn_988 = {FunctionType, -1, "name_impl", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_994}}};


// --------- symbol? --------------
Function fn_995;
Value *arityImpl_996(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_203(empty_list, (Value *)&_num_7, arg0);
return(rslt1);
};


// --------- symbol? main body --------------
Function fn_995 = {FunctionType, -1, "symbol?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_996}}};

struct {int64_t type;
 int32_t refs;
   int64_t len;
   char buffer[2];} _str_62 = {1, -1, 1,":"};

// --------- keyword --------------
Function fn_998;
Value *arityImpl_999(List *closures, Value *arg0) {
List *varArgs1 = empty_list;
incRef((Value *)arg0);
varArgs1 = (List *)listCons((Value *)arg0, varArgs1);
incRef((Value *)(Value *)&_str_62);
varArgs1 = (List *)listCons((Value *)(Value *)&_str_62, varArgs1);
Value *rslt2 = arityImpl_811(empty_list, (Value *)varArgs1);
dec_and_free((Value *)varArgs1);
Value *rslt3 = arityImpl_93(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- keyword main body --------------
Function fn_998 = {FunctionType, -1, "keyword", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_999}}};


// --------- keyword? --------------
Function fn_1001;
Value *arityImpl_1002(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_203(empty_list, (Value *)&_num_5, arg0);
return(rslt1);
};


// --------- keyword? main body --------------
Function fn_1001 = {FunctionType, -1, "keyword?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1002}}};


// --------- number? --------------
Function fn_1004;
Value *arityImpl_1005(List *closures, Value *arg0) {
Value *rslt1 = protoFnImpl_203(empty_list, (Value *)&_num_2, arg0);
return(rslt1);
};


// --------- number? main body --------------
Function fn_1004 = {FunctionType, -1, "number?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1005}}};


// --------- string? --------------
Function fn_1007;
Value *arityImpl_1008(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_99(empty_list, arg0);
Value *rslt2 = arityImpl_442(empty_list, (Value *)&_num_1, rslt1);
Value *rslt3 = arityImpl_99(empty_list, arg0);
Value *rslt4 = arityImpl_442(empty_list, (Value *)&_num_6, rslt3);
List *varArgs5 = empty_list;
incRef((Value *)rslt4);
varArgs5 = (List *)listCons((Value *)rslt4, varArgs5);
incRef((Value *)rslt2);
varArgs5 = (List *)listCons((Value *)rslt2, varArgs5);
Value *rslt6 = arityImpl_438(empty_list, (Value *)varArgs5);
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
Function fn_1007 = {FunctionType, -1, "string?", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1008}}};


// --------- range* --------------
Function fn_1010;
Value *arityImpl_1011(List *closures, Value *arg0) {
Value *cond1;
Value *rslt5 = arityImpl_442(empty_list, (Value *)&_num_13, arg0);

if (isTrue(rslt5)) {
dec_and_free(rslt5);
List *varArgs6 = empty_list;
incRef((Value *)(Value *)&_num_13);
varArgs6 = (List *)listCons((Value *)(Value *)&_num_13, varArgs6);
Value *rslt7 = arityImpl_259(empty_list, (Value *)varArgs6);
dec_and_free((Value *)varArgs6);
incRef(rslt7);
cond1 = rslt7;
dec_and_free(rslt7);
} else {
dec_and_free(rslt5);
Value *rslt2 = arityImpl_743(empty_list, arg0);
Value *rslt3 = arityImpl_1011(closures, rslt2);
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
Function fn_1010 = {FunctionType, -1, "range*", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1011}}};


// --------- range --------------
Function fn_1013;
Value *arityImpl_1014(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_743(empty_list, arg0);
Value *rslt2 = arityImpl_1011(empty_list, rslt1);
Value *rslt3 = arityImpl_607(empty_list, rslt2);
incRef(rslt3);
dec_and_free(rslt1);
dec_and_free(rslt3);
dec_and_free(rslt2);
return(rslt3);
};


// --------- range main body --------------
Function fn_1013 = {FunctionType, -1, "range", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1014}}};


// --------- repeat --------------
Function fn_1016;

// --------- anon --------------
Function fn_1018;
Value *arityImpl_1019(List *closures, Value *arg0) {
Value * val1  = closures->head;
 if (closures->tail)
closures->tail->len = closures->len - 1;
 closures = closures->tail;
incRef(val1);
return(val1);
};

Value *arityImpl_1017(List *closures, Value *arg0, Value *arg1) {
Value *cond2;
Value *rslt7 = arityImpl_589(empty_list, arg0, (Value *)&_num_1);

if (isTrue(rslt7)) {
dec_and_free(rslt7);
incRef(var_129);
cond2 = var_129;
} else {
dec_and_free(rslt7);
Value *rslt3 = arityImpl_743(empty_list, arg0);
Value *rslt4 = arityImpl_1011(empty_list, rslt3);
FnArity *arity_5 = malloc_fnArity();
arity_5->type = FnArityType;
arity_5->count = 1;
arity_5->closures = empty_list;
arity_5->variadic = 0;
arity_5->fn = arityImpl_1019;
incRef((Value *)arg1);
arity_5->closures = listCons((Value *)arg1, (List *)arity_5->closures);
Function *fn_1018 = malloc_function(1);
fn_1018->type = FunctionType;
fn_1018->name = "anon";
fn_1018->arityCount = 1;
fn_1018->arities[0] = arity_5;
Value *rslt6 = arityImpl_708(empty_list, rslt4, (Value *)fn_1018);
incRef(rslt6);
cond2 = rslt6;
dec_and_free(rslt6);
dec_and_free((Value *)fn_1018);
dec_and_free(rslt4);
dec_and_free(rslt3);
}
return(cond2);
};


// --------- repeat main body --------------
Function fn_1016 = {FunctionType, -1, "repeat", 1, {&(FnArity){FnArityType, -1, 2, (List *)0, 0, arityImpl_1017}}};


 int64_t sym_counter = 0;

// --------- get-sym-count --------------
Function fn_1021;
Value *arityImpl_1022(List *closures) {

  return numberValue(sym_counter);
};


// --------- get-sym-count main body --------------
Function fn_1021 = {FunctionType, -1, "get-sym-count", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_1022}}};


// --------- set-sym-count --------------
Function fn_1024;
Value *arityImpl_1025(List *closures, Value *arg0) {

  sym_counter = ((Number *)arg0)->numVal;
  return true;
};


// --------- set-sym-count main body --------------
Function fn_1024 = {FunctionType, -1, "set-sym-count", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1025}}};


// --------- new-sym-count --------------
Function fn_1027;
Value *arityImpl_1028(List *closures) {

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
Function fn_1027 = {FunctionType, -1, "new-sym-count", 1, {&(FnArity){FnArityType, -1, 0, (List *)0, 0, arityImpl_1028}}};


// --------- gensym --------------
Function fn_1030;
Value *arityImpl_1031(List *closures, Value *arg0) {
Value *rslt1 = arityImpl_1028(empty_list);
List *varArgs2 = empty_list;
incRef((Value *)rslt1);
varArgs2 = (List *)listCons((Value *)rslt1, varArgs2);
incRef((Value *)arg0);
varArgs2 = (List *)listCons((Value *)arg0, varArgs2);
Value *rslt3 = arityImpl_811(empty_list, (Value *)varArgs2);
dec_and_free((Value *)varArgs2);
Value *rslt4 = arityImpl_90(empty_list, rslt3);
incRef(rslt4);
dec_and_free(rslt1);
dec_and_free(rslt4);
dec_and_free(rslt3);
return(rslt4);
};


// --------- gensym main body --------------
Function fn_1030 = {FunctionType, -1, "gensym", 1, {&(FnArity){FnArityType, -1, 1, (List *)0, 0, arityImpl_1031}}};

Value *get(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_392((List *)0, node, key, val, hash, shift));
}
Value *assoc(Value *node, Value *key, Value *val, Value *hash, Value *shift) {
  return(protoFnImpl_394((List *)0, node, key, val, hash, shift));
}
Value *valsEqual(List *x, Value *v1, Value *v2) {
  return(protoFnImpl_291(x, v1, v2));
}
Value *sha1(Value *v) {
  return(protoFnImpl_427((List *)0, v));
}
Value *hashSeq(Value *n, Value *s) {
  return(protoFnImpl_396((List *)0, n, s));
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
strInfo = listCons(stringValue("_str_58"), empty_list);
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
strInfo = listCons(stringValue("_str_45"), empty_list);
strInfo = listCons(stringValue("&"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_55"), empty_list);
strInfo = listCons(stringValue("\n*** "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_46"), empty_list);
strInfo = listCons(stringValue("<maybe "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_56"), empty_list);
strInfo = listCons(stringValue(""), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_40"), empty_list);
strInfo = listCons(stringValue("'string-list' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_44"), empty_list);
strInfo = listCons(stringValue("<nothing>"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_37"), empty_list);
strInfo = listCons(stringValue("'<*' not implemented:"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_53"), empty_list);
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
strInfo = listCons(stringValue("_str_38"), empty_list);
strInfo = listCons(stringValue("*** 'wrap' not implemented"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_18"), empty_list);
strInfo = listCons(stringValue("Value *"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_51"), empty_list);
strInfo = listCons(stringValue(", "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_13"), empty_list);
strInfo = listCons(stringValue("char"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_9"), empty_list);
strInfo = listCons(stringValue("Function"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_41"), empty_list);
strInfo = listCons(stringValue("'serialize' not implemented for type"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_2"), empty_list);
strInfo = listCons(stringValue("SubStr"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_39"), empty_list);
strInfo = listCons(stringValue("'name' not implemented for type "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_22"), empty_list);
strInfo = listCons(stringValue("typedef struct List {int64_t type; int32_t refs; int64_t len; Value* head; struct List *tail;} List;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_48"), empty_list);
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
strInfo = listCons(stringValue("_str_54"), empty_list);
strInfo = listCons(stringValue("\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_61"), empty_list);
strInfo = listCons(stringValue("Could not look up "), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_49"), empty_list);
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
strInfo = listCons(stringValue("_str_47"), empty_list);
strInfo = listCons(stringValue(">"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_12"), empty_list);
strInfo = listCons(stringValue("void"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_50"), empty_list);
strInfo = listCons(stringValue("("), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_28"), empty_list);
strInfo = listCons(stringValue("typedef struct {int64_t type; int32_t refs; void *ptr;} Opaque;\n"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_52"), empty_list);
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
strInfo = listCons(stringValue("_str_62"), empty_list);
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
strInfo = listCons(stringValue("_str_60"), empty_list);
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
strInfo = listCons(stringValue("_str_57"), empty_list);
strInfo = listCons(stringValue("'nth' from empty seq"), strInfo);
strs = listCons((Value *)strInfo, strs);
strInfo = listCons(stringValue("_str_59"), empty_list);
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
impl = listCons(stringValue("(Value *)&protoFn_539"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue(".v"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_504;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_503"), protoInfo);
protoInfo = listCons(stringValue("Getter/.v"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_519"), impl);
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
impl = listCons(stringValue("(Value *)&fn_660"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_752"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_782"), impl);
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
impl = listCons(stringValue("(Value *)&fn_668"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_529"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_614"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_885"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_853"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_917"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_756"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_786"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_461"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("comp*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_363;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_362"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/comp*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_669"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_951"), impl);
impl = listCons(numberValue(17), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_974"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_757"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_984"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_787"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_626"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_463"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_289"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("=*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_288;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_287"), protoInfo);
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
impl = listCons(stringValue("(Value *)&fn_664"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("crush"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_358;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_357"), protoInfo);
protoInfo = listCons(stringValue("core/Crushable/crush"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_663"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_755"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_785"), impl);
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
impl = listCons(stringValue("(Value *)&defaultFn_283"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("serialize"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_282;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_281"), protoInfo);
protoInfo = listCons(stringValue("core/Serializable/serialize"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_658"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("traverse"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_353;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_352"), protoInfo);
protoInfo = listCons(stringValue("core/Traversable/traverse"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_888"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_856"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_920"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("vals"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_405;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_404"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/vals"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_675"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_533"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_467"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_263"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("map"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_262;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_261"), protoInfo);
protoInfo = listCons(stringValue("core/Functor/map"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_973"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_750"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_983"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_780"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_624"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("sha1"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_425;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_424"), protoInfo);
protoInfo = listCons(stringValue("core/Hash/sha1"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_977"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_988"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_271"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("name"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_270;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_269"), protoInfo);
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
impl = listCons(stringValue("(Value *)&fn_892"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_860"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_924"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("hash-seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_390;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_389"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/hash-seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_525"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_612"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_510"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_457"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_247"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("apply*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_246;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_245"), protoInfo);
protoInfo = listCons(stringValue("core/Applicative/apply*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_665"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_521"), impl);
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
impl = listCons(stringValue("(Value *)&fn_673"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_761"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_791"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_330;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_329"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/first"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_662"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_882"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_850"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_914"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_753"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_783"), impl);
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
impl = listCons(stringValue("(Value *)&fn_886"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_854"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_918"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_409"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_408;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_407"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/get"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_894"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_862"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_926"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("get*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_384;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_383"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/get*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_893"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_861"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_925"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_387;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_386"), protoInfo);
protoInfo = listCons(stringValue("core/HashMapNode/assoc*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_37"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_537"), impl);
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
impl = listCons(stringValue("(Value *)&fn_887"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_855"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_919"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("keys"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_411;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_410"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/keys"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_976"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_512"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_987"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_568"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_471"), impl);
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
impl = listCons(stringValue("(Value *)&fn_666"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_523"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_455"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_244"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("wrap"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_243;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_242"), protoInfo);
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
impl = listCons(stringValue("(Value *)&protoFn_514"), impl);
impl = listCons(numberValue(14), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_570"), impl);
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
impl = listCons(stringValue("(Value *)&fn_659"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_883"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_851"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_915"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_751"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_781"), impl);
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
impl = listCons(stringValue("(Value *)&fn_676"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_535"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_469"), impl);
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
impl = listCons(stringValue("(Value *)&fn_671"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_891"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_859"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_923"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_759"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_789"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_327;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_326"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/seq"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_625"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_237"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("<*"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_236;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_235"), protoInfo);
protoInfo = listCons(stringValue("core/Ord/<*"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_672"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_760"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_790"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("m-first"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_333;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_332"), protoInfo);
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
protoInfo = listCons(stringValue("extern Function protoFn_402;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_401"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/dissoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_670"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_337"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("seq?"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_336;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_335"), protoInfo);
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
impl = listCons(stringValue("(Value *)&fn_661"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_754"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_784"), impl);
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
impl = listCons(stringValue("(Value *)&fn_674"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_762"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_792"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("rest"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_324;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_323"), protoInfo);
protoInfo = listCons(stringValue("core/Seqable/rest"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_889"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_857"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_921"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("assoc"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_399;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_398"), protoInfo);
protoInfo = listCons(stringValue("core/Associative/assoc"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_667"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_527"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_613"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_884"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_852"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_916"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_566"), impl);
impl = listCons(numberValue(16), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_459"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("zero"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_366;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_365"), protoInfo);
protoInfo = listCons(stringValue("core/Monoid/zero"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
protoInfo = empty_list;
impls = empty_list;
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_715"), impl);
impl = listCons(numberValue(4), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_531"), impl);
impl = listCons(numberValue(15), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_615"), impl);
impl = listCons(numberValue(3), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_890"), impl);
impl = listCons(numberValue(11), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_975"), impl);
impl = listCons(numberValue(5), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_858"), impl);
impl = listCons(numberValue(10), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_922"), impl);
impl = listCons(numberValue(12), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_758"), impl);
impl = listCons(numberValue(1), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_985"), impl);
impl = listCons(numberValue(7), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_788"), impl);
impl = listCons(numberValue(6), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&fn_627"), impl);
impl = listCons(numberValue(2), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&protoFn_465"), impl);
impl = listCons(numberValue(13), impl);
impls = listCons((Value *)impl, impls);
impl = empty_list;
impl = listCons(stringValue("(Value *)&defaultFn_277"), impl);
impl = listCons(keywordValue(":default"), impl);
impls = listCons((Value *)impl, impls);
protoInfo = listCons(symbolValue("string-list"), protoInfo);
protoInfo = listCons((Value *)impls, protoInfo);
protoInfo = listCons(stringValue("extern Function protoFn_276;"), protoInfo);
protoInfo = listCons(stringValue("protoImpls_275"), protoInfo);
protoInfo = listCons(stringValue("core/Stringable/string-list"), protoInfo);
protos = listCons((Value *)protoInfo, protos);
return((Value *)protos);
}

Value *static_fns() {
List *staticFns = empty_list;
List *fnInfo;
List *arityInfo;
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_841"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_840"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_839"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_778"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_761"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_701"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_947"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
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
arityInfo = listCons(stringValue("protoImpl_497"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_471"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_285"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_634"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_635"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_633"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_417"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_405"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_682"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_660"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_583"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_581"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_582"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_580"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1005"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1004"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_493"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_467"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_945"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_926"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_897"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_884"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_572"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_567"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("protoImpl_560"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_537"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_618"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_614"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_991"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_985"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_911"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_892"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_865"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_852"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_929"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_916"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_938"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_921"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_427"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_425"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_980"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_975"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_394"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_387"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_935"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_918"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_728"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_53"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_648"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_368"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_363"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_434"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_433"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_432"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_517"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_510"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_906"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_889"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_764"), arityInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1028"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1027"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_799"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_786"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_805"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_788"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_909"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_340"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_327"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_875"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_858"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_767"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_754"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_599"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_598"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_941"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_940"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_953"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_952"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_994"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_988"), fnInfo);
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
arityInfo = listCons(stringValue("protoImpl_564"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_514"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_700"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_670"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_721"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
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
arityInfo = listCons(stringValue("protoImpl_476"), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_936"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_919"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_683"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_661"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_677"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_658"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_965"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_964"), fnInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_506"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_504"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_708"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_675"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_793"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_780"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_422"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_411"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_553"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_532"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_576"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_571"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_806"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_789"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_630"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_626"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_724"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_723"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_834"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_833"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_259"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_258"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_944"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_925"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_735"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_733"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_734"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_732"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_490"), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_396"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_390"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_548"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_482"), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_279"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_276"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_551"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_530"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1002"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1001"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_982"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_977"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_954"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_951"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_360"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_358"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_616"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_612"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_844"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_843"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoImpl_546"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_523"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_577"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_570"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_338"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_324"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_996"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_995"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_495"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_469"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_617"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_613"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1017"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1016"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_743"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_742"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_813"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_812"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_629"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_625"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_684"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_662"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_488"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_464"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_558"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_535"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_981"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_976"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_796"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_783"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_699"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_669"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_879"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_860"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoImpl_575"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_568"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_350"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_349"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_942"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_923"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_768"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_755"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_706"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_673"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_685"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_663"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_818"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_477"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_456"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_483"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_462"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_593"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_592"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(3), empty_list);
arityInfo = listCons(stringValue("arityImpl_639"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_637"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_479"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_458"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_968"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_967"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_949"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_948"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_707"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_674"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_716"), arityInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_623"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_615"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_990"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_496"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_472"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_256"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_246"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_544"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_521"), fnInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_602"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_601"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_794"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_781"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_870"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_869"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_481"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_460"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_653"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_907"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_890"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_342"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_330"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_645"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_644"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_509"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_450"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_420"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_408"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_863"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_850"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_552"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_529"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_596"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_595"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_898"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_885"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_937"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_920"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1014"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1013"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_808"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_791"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_958"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_957"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_698"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_668"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_864"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_851"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_992"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_986"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_373"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_372"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_795"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_782"), fnInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_837"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_836"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_590"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_589"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_588"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_702"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_672"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_874"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_857"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_811"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_810"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_501"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_500"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_355"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_353"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_711"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_710"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_765"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_752"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_774"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_757"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_478"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_455"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_809"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_792"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_807"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_790"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_475"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_454"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_831"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_830"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_728"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_727"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_927"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_914"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_978"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_973"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_480"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_457"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_766"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_753"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_913"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_894"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_392"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_384"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_740"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_738"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_739"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_737"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_562"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_539"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_989"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_983"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_804"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_787"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_430"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_429"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_381"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_380"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_379"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_542"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_519"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_509"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_512"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_730"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_729"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_777"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_760"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_607"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_606"), fnInfo);
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
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("protoImpl_573"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_566"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_377"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_376"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_516"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_511"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_697"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_667"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_797"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_784"), fnInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_239"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_236"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_824"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_825"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_823"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_993"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_344"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_333"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_776"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_759"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_634"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_635"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("var_241"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_492"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_468"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_881"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_862"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_934"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_933"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_798"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_785"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_828"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_912"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_763"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_750"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_769"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(stringValue("arityImpl_900"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_899"), fnInfo);
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
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_689"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_664"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_718"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_717"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_696"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_666"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_586"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_585"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(7), empty_list);
arityInfo = listCons(stringValue("arityImpl_1031"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1030"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_370"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_366"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_1011"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1010"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_905"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_888"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_872"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_855"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1022"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1021"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_267"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_262"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_943"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_924"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_895"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_882"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_910"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_891"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_971"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_970"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_866"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_853"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_904"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_887"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("protoImpl_550"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_527"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_518"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_513"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_871"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_854"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_610"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_609"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_474"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_451"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_930"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_775"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_758"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_928"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_915"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_748"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_746"), arityInfo);
arityInfo = listCons(numberValue(0), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_747"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_745"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_779"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_762"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("protoImpl_491"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_465"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_801"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_800"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_494"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_470"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_868"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_867"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_650"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
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
arityInfo = listCons(numberValue(5), empty_list);
arityInfo = listCons(stringValue("arityImpl_93"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_92"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_821"), arityInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_203"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_200"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_896"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_883"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_1025"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1024"), fnInfo);
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
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_545"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_524"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_709"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_676"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_413"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_399"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_979"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_974"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(13), empty_list);
arityInfo = listCons(stringValue("arityImpl_549"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_528"), fnInfo);
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
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_177"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_176"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_880"), arityInfo);
arityInfo = listCons(numberValue(5), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_861"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_563"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_515"), fnInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_631"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_627"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_438"), arityInfo);
arityInfo = listCons(keywordValue(":variadic"), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_437"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_436"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_877"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_876"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_878"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_859"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(1), empty_list);
arityInfo = listCons(stringValue("arityImpl_559"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_538"), fnInfo);
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
arityInfo = listCons(stringValue("arityImpl_622"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_621"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("protoImpl_489"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_463"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_903"), arityInfo);
arityInfo = listCons(numberValue(3), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_886"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_556"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_533"), fnInfo);
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
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_681"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_659"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_473"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_452"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_932"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_931"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(15), empty_list);
arityInfo = listCons(stringValue("arityImpl_574"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_569"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_1008"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_1007"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoFnImpl_249"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_243"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_692"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_665"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_902"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
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
arityInfo = listCons(numberValue(4), empty_list);
arityInfo = listCons(stringValue("arityImpl_939"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_922"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_628"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_624"), fnInfo);
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
arityInfo = listCons(stringValue("protoFnImpl_415"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_402"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_487"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_461"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(5), empty_list);
arityInfo = listCons(stringValue("arityImpl_999"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_998"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_873"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_856"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("protoImpl_554"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&protoFn_531"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(keywordValue(":no-type"), empty_list);
arityInfo = listCons(stringValue("arityImpl_847"), arityInfo);
arityInfo = listCons(numberValue(1), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_846"), fnInfo);
staticFns = listCons((Value *)fnInfo, staticFns);
fnInfo = empty_list;
arityInfo = listCons(numberValue(2), empty_list);
arityInfo = listCons(stringValue("arityImpl_771"), arityInfo);
arityInfo = listCons(numberValue(2), arityInfo);
fnInfo = listCons((Value *)arityInfo, fnInfo);
fnInfo = listCons((Value *)fnInfo, empty_list);
fnInfo = listCons(stringValue("(Value *)&fn_770"), fnInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_324"), symInfo);
symInfo = listCons(stringValue("Function protoFn_324"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("rest"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_925"), symInfo);
symInfo = listCons(stringValue("Function fn_925"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(16), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_578"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_578"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("maybe"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_327"), symInfo);
symInfo = listCons(stringValue("Function protoFn_327"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_243"), symInfo);
symInfo = listCons(stringValue("Function protoFn_243"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("wrap"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_720"), symInfo);
symInfo = listCons(stringValue("Function fn_720"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("print"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_349"), symInfo);
symInfo = listCons(stringValue("Function fn_349"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_923"), symInfo);
symInfo = listCons(stringValue("Function fn_923"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_717"), symInfo);
symInfo = listCons(stringValue("Function fn_717"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_957"), symInfo);
symInfo = listCons(stringValue("Function fn_957"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("merge-with"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_647"), symInfo);
symInfo = listCons(stringValue("Function fn_647"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_588"), symInfo);
symInfo = listCons(stringValue("Function fn_588"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_625"), symInfo);
symInfo = listCons(stringValue("Function fn_625"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_967"), symInfo);
symInfo = listCons(stringValue("Function fn_967"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("update-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_384"), symInfo);
symInfo = listCons(stringValue("Function protoFn_384"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_399"), symInfo);
symInfo = listCons(stringValue("Function protoFn_399"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_964"), symInfo);
symInfo = listCons(stringValue("Function fn_964"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_729"), symInfo);
symInfo = listCons(stringValue("Function fn_729"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_665"), symInfo);
symInfo = listCons(stringValue("Function fn_665"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("flat-map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1021"), symInfo);
symInfo = listCons(stringValue("Function fn_1021"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get-sym-count"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_644"), symInfo);
symInfo = listCons(stringValue("Function fn_644"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_363"), symInfo);
symInfo = listCons(stringValue("Function protoFn_363"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_742"), symInfo);
symInfo = listCons(stringValue("Function fn_742"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dec"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_387"), symInfo);
symInfo = listCons(stringValue("Function protoFn_387"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(keywordValue(":no-type"), empty_list);
symInfo = listCons(stringValue("var_849"), symInfo);
symInfo = listCons(stringValue("Value *var_849;"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("emptyBMI"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_790"), symInfo);
symInfo = listCons(stringValue("Function fn_790"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("m-first_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_330"), symInfo);
symInfo = listCons(stringValue("Function protoFn_330"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_946"), symInfo);
symInfo = listCons(stringValue("Function fn_946"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_823"), symInfo);
symInfo = listCons(stringValue("Function fn_823"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("split"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_270"), symInfo);
symInfo = listCons(stringValue("Function protoFn_270"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_792"), symInfo);
symInfo = listCons(stringValue("Function fn_792"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_366"), symInfo);
symInfo = listCons(stringValue("Function protoFn_366"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_288"), symInfo);
symInfo = listCons(stringValue("Function protoFn_288"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("=*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_921"), symInfo);
symInfo = listCons(stringValue("Function fn_921"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_540"), symInfo);
symInfo = listCons(stringValue("Function fn_540"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_983"), symInfo);
symInfo = listCons(stringValue("Function fn_983"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_258"), symInfo);
symInfo = listCons(stringValue("Function fn_258"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_436"), symInfo);
symInfo = listCons(stringValue("Function fn_436"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_1024"), symInfo);
symInfo = listCons(stringValue("Function fn_1024"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&reified_955"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_955"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("not-found"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_710"), symInfo);
symInfo = listCons(stringValue("Function fn_710"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("interpose"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1030"), symInfo);
symInfo = listCons(stringValue("Function fn_1030"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("gensym"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_984"), symInfo);
symInfo = listCons(stringValue("Function fn_984"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_916"), symInfo);
symInfo = listCons(stringValue("Function fn_916"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("zero_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_633"), symInfo);
symInfo = listCons(stringValue("Function fn_633"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_598"), symInfo);
symInfo = listCons(stringValue("Function fn_598"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_675"), symInfo);
symInfo = listCons(stringValue("Function fn_675"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_276"), symInfo);
symInfo = listCons(stringValue("Function protoFn_276"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_580"), symInfo);
symInfo = listCons(stringValue("Function fn_580"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_1001"), symInfo);
symInfo = listCons(stringValue("Function fn_1001"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_246"), symInfo);
symInfo = listCons(stringValue("Function protoFn_246"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_920"), symInfo);
symInfo = listCons(stringValue("Function fn_920"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_612"), symInfo);
symInfo = listCons(stringValue("Function fn_612"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_1016"), symInfo);
symInfo = listCons(stringValue("Function fn_1016"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("repeat"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_282"), symInfo);
symInfo = listCons(stringValue("Function protoFn_282"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("serialize"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1004"), symInfo);
symInfo = listCons(stringValue("Function fn_1004"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_402"), symInfo);
symInfo = listCons(stringValue("Function protoFn_402"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("dissoc"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_926"), symInfo);
symInfo = listCons(stringValue("Function fn_926"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get*_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_262"), symInfo);
symInfo = listCons(stringValue("Function protoFn_262"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("map"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_595"), symInfo);
symInfo = listCons(stringValue("Function fn_595"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_970"), symInfo);
symInfo = listCons(stringValue("Function fn_970"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("assoc-in"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_723"), symInfo);
symInfo = listCons(stringValue("Function fn_723"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("println"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1013"), symInfo);
symInfo = listCons(stringValue("Function fn_1013"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_333"), symInfo);
symInfo = listCons(stringValue("Function protoFn_333"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_520"), symInfo);
symInfo = listCons(stringValue("Function fn_520"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_390"), symInfo);
symInfo = listCons(stringValue("Function protoFn_390"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("hash-seq"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_791"), symInfo);
symInfo = listCons(stringValue("Function fn_791"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_784"), symInfo);
symInfo = listCons(stringValue("Function fn_784"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("conj_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_727"), symInfo);
symInfo = listCons(stringValue("Function fn_727"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_429"), symInfo);
symInfo = listCons(stringValue("Function fn_429"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_833"), symInfo);
symInfo = listCons(stringValue("Function fn_833"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_914"), symInfo);
symInfo = listCons(stringValue("Function fn_914"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("count_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_379"), symInfo);
symInfo = listCons(stringValue("Function fn_379"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_917"), symInfo);
symInfo = listCons(stringValue("Function fn_917"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_919"), symInfo);
symInfo = listCons(stringValue("Function fn_919"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_571"), symInfo);
symInfo = listCons(stringValue("Function fn_571"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("instance?_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_609"), symInfo);
symInfo = listCons(stringValue("Function fn_609"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("identity"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1018"), symInfo);
symInfo = listCons(stringValue("Function fn_1018"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("anon"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_839"), symInfo);
symInfo = listCons(stringValue("Function fn_839"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_585"), symInfo);
symInfo = listCons(stringValue("Function fn_585"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_432"), symInfo);
symInfo = listCons(stringValue("Function fn_432"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_375"), symInfo);
symInfo = listCons(stringValue("Function fn_375"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_843"), symInfo);
symInfo = listCons(stringValue("Function fn_843"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_1007"), symInfo);
symInfo = listCons(stringValue("Function fn_1007"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_745"), symInfo);
symInfo = listCons(stringValue("Function fn_745"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_236"), symInfo);
symInfo = listCons(stringValue("Function protoFn_236"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("<*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(13), empty_list);
symInfo = listCons(stringValue("(Value *)&reified_498"), symInfo);
symInfo = listCons(stringValue("ReifiedVal reified_498"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_358"), symInfo);
symInfo = listCons(stringValue("Function protoFn_358"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("crush"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_353"), symInfo);
symInfo = listCons(stringValue("Function protoFn_353"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_500"), symInfo);
symInfo = listCons(stringValue("Function fn_500"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("any?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_538"), symInfo);
symInfo = listCons(stringValue("Function fn_538"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_737"), symInfo);
symInfo = listCons(stringValue("Function fn_737"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_987"), symInfo);
symInfo = listCons(stringValue("Function fn_987"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("invoke_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_405"), symInfo);
symInfo = listCons(stringValue("Function protoFn_405"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("vals"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_732"), symInfo);
symInfo = listCons(stringValue("Function fn_732"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("+"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_998"), symInfo);
symInfo = listCons(stringValue("Function fn_998"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_601"), symInfo);
symInfo = listCons(stringValue("Function fn_601"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_785"), symInfo);
symInfo = listCons(stringValue("Function fn_785"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&protoFn_425"), symInfo);
symInfo = listCons(stringValue("Function protoFn_425"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("sha1"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_846"), symInfo);
symInfo = listCons(stringValue("Function fn_846"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("butlast"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_918"), symInfo);
symInfo = listCons(stringValue("Function fn_918"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_995"), symInfo);
symInfo = listCons(stringValue("Function fn_995"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_810"), symInfo);
symInfo = listCons(stringValue("Function fn_810"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("str"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_658"), symInfo);
symInfo = listCons(stringValue("Function fn_658"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_670"), symInfo);
symInfo = listCons(stringValue("Function fn_670"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_817"), symInfo);
symInfo = listCons(stringValue("Function fn_817"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("take"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1027"), symInfo);
symInfo = listCons(stringValue("Function fn_1027"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_606"), symInfo);
symInfo = listCons(stringValue("Function fn_606"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reverse"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_408"), symInfo);
symInfo = listCons(stringValue("Function protoFn_408"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("get"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_652"), symInfo);
symInfo = listCons(stringValue("Function fn_652"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("reduce-list"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_782"), symInfo);
symInfo = listCons(stringValue("Function fn_782"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("empty_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_1010"), symInfo);
symInfo = listCons(stringValue("Function fn_1010"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("range*"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_372"), symInfo);
symInfo = listCons(stringValue("Function fn_372"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("apply"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_830"), symInfo);
symInfo = listCons(stringValue("Function fn_830"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("remove-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_915"), symInfo);
symInfo = listCons(stringValue("Function fn_915"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_676"), symInfo);
symInfo = listCons(stringValue("Function fn_676"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("type-args_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_820"), symInfo);
symInfo = listCons(stringValue("Function fn_820"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_985"), symInfo);
symInfo = listCons(stringValue("Function fn_985"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("string-list_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_924"), symInfo);
symInfo = listCons(stringValue("Function fn_924"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_827"), symInfo);
symInfo = listCons(stringValue("Function fn_827"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("replace-at-nth"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_836"), symInfo);
symInfo = listCons(stringValue("Function fn_836"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_666"), symInfo);
symInfo = listCons(stringValue("Function fn_666"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_592"), symInfo);
symInfo = listCons(stringValue("Function fn_592"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("list**"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&fn_988"), symInfo);
symInfo = listCons(stringValue("Function fn_988"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("name_impl"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_411"), symInfo);
symInfo = listCons(stringValue("Function protoFn_411"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("keys"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_336"), symInfo);
symInfo = listCons(stringValue("Function protoFn_336"), symInfo);
symInfo = listCons((Value *)symInfo, empty_list);
symInfo = listCons(symbolValue("seq?"), symInfo);
defSyms = listCons((Value *)symInfo, defSyms);
symInfo = listCons(numberValue(3), empty_list);
symInfo = listCons(stringValue("(Value *)&protoFn_504"), symInfo);
symInfo = listCons(stringValue("Function protoFn_504"), symInfo);
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
symInfo = listCons(stringValue("(Value *)&fn_664"), symInfo);
symInfo = listCons(stringValue("Function fn_664"), symInfo);
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
cnts = listCons(numberValue(1033), cnts);
return((Value *)cnts);
}

