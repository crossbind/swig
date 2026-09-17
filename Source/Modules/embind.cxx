#include "swigmod.h"
#include "cparse.h"
#include <ctype.h>
#include <iostream>

static const char *usage = (char *) "";

int findStartOfParenthesis(std::string s) {
  bool start = false;
  int count = 0;
  for (int i = s.length() - 1; i >= 0; i -= 1) {
    if (!start && s[i] == ')') {
      start = true;
      count = 1;
    } else if (start && s[i] == ')') {
      count += 1;
    } else if (start && s[i] == '(') {
      count -= 1;
      if (count == 0) {
        return i;
      }
    }
  }
  return -1;
}

int findEndOfParenthesisOrBlank(std::string s) {
  for (int i = s.length() - 1; i >= 0; i -= 1) {
    if (s[i] == ')' || s[i] == ' ') {
      return i;
    }
  }
  return -1;
}

// Pointer-free types keep the Split-based spelling so bridges generated before pointer support stay byte-identical.
static bool spellsPointer(const SwigType *t) {
  const char *s = Char(t);
  for (const char *c = s; *c; ++c) {
    bool atElement = c == s || c[-1] == '.' || c[-1] == '(' || c[-1] == ',';
    if (atElement && (strncmp(c, "p.", 2) == 0 || strncmp(c, "a(", 2) == 0)) return true;
  }
  return false;
}

static SwigType *bareType(const SwigType *t) {
  SwigType *resolved = SwigType_typedef_resolve_all(t);
  if (SwigType_isreference(resolved)) SwigType_del_reference(resolved);
  else if (SwigType_isrvalue_reference(resolved)) SwigType_del_rvalue_reference(resolved);
  SwigType *bare = SwigType_strip_qualifiers(resolved);
  Delete(resolved);
  return bare;
}

static bool isRawPointer(const SwigType *t) {
  SwigType *bare = bareType(t);
  bool result = SwigType_ispointer(bare) || SwigType_isarray(bare);
  Delete(bare);
  return result;
}

static bool takesVariadicArguments(ParmList *parms) {
  for (Parm *p = parms; p; p = nextSibling(p)) {
    if (SwigType_isvarargs(Getattr(p, "type"))) return true;
    SwigType *bare = bareType(Getattr(p, "type"));
    bool isVaList = Strcmp(bare, "va_list") == 0 || Strcmp(bare, "std::va_list") == 0 || Strcmp(bare, "__builtin_va_list") == 0 || Strcmp(bare, "__gnuc_va_list") == 0;
    Delete(bare);
    if (isVaList) return true;
  }
  return false;
}

// SWIG never resolves an alias template such as GEOS's private `using TriList = tri::TriList<TriType>;`, so its template
// arguments are substituted into the target. A public one keeps its own spelling.
static SwigType *expandPrivateAliasTemplate(const SwigType *t, const String *scope) {
  SwigType *base = SwigType_base(t);
  String *templatePrefix = SwigType_templateprefix(base);
  String *owner = Swig_scopename_prefix(templatePrefix);
  Node *alias = owner && Equal(owner, scope) ? Swig_symbol_clookup(templatePrefix, 0) : 0;
  String *access = alias ? Getattr(alias, "access") : 0;
  String *templateArgs = SwigType_templateargs(base);
  SwigType *expanded = 0;
  if (alias && GetFlag(alias, "aliastemplate") && access && !Equal(access, "public") && templateArgs) {
    SwigType *target = Copy(Getattr(alias, "type"));
    List *args = SwigType_parmlist(templateArgs);
    int index = 0;
    for (Parm *p = Getattr(alias, "templateparms"); p && index < Len(args); p = nextSibling(p), index++) {
      Replaceid(target, Getattr(p, "name"), Getitem(args, index));
    }
    String *prefix = SwigType_prefix(t);
    expanded = NewStringf("%s%s", prefix, target);
    Delete(prefix);
    Delete(args);
    Delete(target);
  }
  Delete(templateArgs);
  Delete(owner);
  Delete(templatePrefix);
  Delete(base);
  return expanded;
}

// A member alias such as `using Coordinate = geom::Coordinate;` is usually private: spell its target.
static SwigType *withoutMemberAliases(const SwigType *t, const String *scope) {
  SwigType *resolved = Copy(t);
  if (!scope || Len(scope) == 0) return resolved;
  String *prefix = NewStringf("%s::", scope);
  while (Strstr(resolved, prefix)) {
    SwigType *next = SwigType_typedef_resolve(resolved);
    if (!next) next = expandPrivateAliasTemplate(resolved, scope);
    if (!next) break;
    Delete(resolved);
    resolved = next;
  }
  Delete(prefix);
  return resolved;
}

static List *enclosingNamespaces(Node *n) {
  List *names = NewList();
  for (Node *p = parentNode(n); p; p = parentNode(p)) {
    if (Equal(nodeType(p), "namespace")) Insert(names, 0, Getattr(p, "name") ? Getattr(p, "name") : NewString(""));
  }
  return names;
}

// A struct from another header or a typedef SWIG never parsed; in C++ SWIG knows every class this interface defines.
static bool isUnknownUserType(Node *n, const SwigType *bare) {
  if (SwigType_type(bare) != T_USER || !SwigType_issimple(bare)) return false;
  return Swig_storage_isexternc(n) || (Strncmp(bare, "std::", 5) != 0 && !Language::classLookup(bare));
}

static bool isNumberCode(int code) {
  switch (code) {
  case T_BOOL: case T_SCHAR: case T_UCHAR: case T_SHORT: case T_USHORT: case T_INT: case T_UINT: case T_LONG: case T_ULONG:
  case T_LONGLONG: case T_ULONGLONG: case T_FLOAT: case T_DOUBLE: case T_LONGDOUBLE: case T_WCHAR:
    return true;
  default:
    return false;
  }
}

// SWIG misparses a function type typedef with a parenthesised name inside a class (GEOS's `typedef void (Callback)(void);`)
// as a constructor named after the return type that takes the typedef name, so it never learns the type.
static bool isMisparsedFunctionTypedef(Node *member, const SwigType *name) {
  String *storage = Getattr(member, "storage");
  ParmList *parms = Getattr(member, "parms");
  String *parmType = parms ? Getattr(parms, "type") : 0;
  return Equal(nodeType(member), "constructor") && storage && Equal(storage, "typedef") && parms && !nextSibling(parms) && parmType && Equal(parmType, name);
}

// SWIG can leave a member type unqualified in a member's signature (GEOS's `static Callback* registerCallback(Callback*)`
// inside geos::util::Interrupt); qualified, it can be spelled in the bridge. A function type typedef SWIG misparsed is
// flagged, since only C++ knows what it names.
static SwigType *qualifyMemberType(Node *n, const SwigType *t, bool *isFunctionTypedef = 0) {
  Node *cls = parentNode(n);
  if (cls && Equal(nodeType(cls), "extend")) cls = parentNode(cls);
  SwigType *base = SwigType_base(t);
  SwigType *qualified = 0;
  if (cls && Equal(nodeType(cls), "class") && SwigType_type(base) == T_USER && !Strstr(base, "::")) {
    for (Node *member = firstChild(cls); member && !qualified; member = nextSibling(member)) {
      String *memberName = Getattr(member, "name");
      String *storage = Getattr(member, "storage");
      String *kind = Getattr(member, "kind");
      bool isMisparsed = isMisparsedFunctionTypedef(member, base);
      bool isNamedType = memberName && Equal(memberName, base) && (Equal(nodeType(member), "class") || Equal(nodeType(member), "classforward") || Equal(nodeType(member), "enum") || (storage && Equal(storage, "typedef")) || (kind && Equal(kind, "typedef")));
      if (isMisparsed || isNamedType) {
        String *prefix = SwigType_prefix(t);
        qualified = NewStringf("%s%s::%s", prefix, Getattr(cls, "name"), base);
        Delete(prefix);
        if (isFunctionTypedef) *isFunctionTypedef = isMisparsed;
      }
    }
  }
  Delete(base);
  return qualified ? qualified : Copy(t);
}

// Pointers and arrays of void, char, numbers, pointers and unknown user types reach JS as crossbind::JsPointer, which
// C++ resolves to the bound class (a complete class) or to a NativePointer handle.
static SwigType *handlePointee(Node *n, const SwigType *t) {
  bool isFunctionTypedef = false;
  SwigType *qualified = qualifyMemberType(n, t, &isFunctionTypedef);
  if (isFunctionTypedef) {
    Delete(qualified);
    return 0;
  }
  SwigType *resolved = SwigType_typedef_resolve_all(qualified);
  Delete(qualified);
  if (SwigType_isqualifier(resolved)) SwigType_del_qualifier(resolved);
  SwigType *pointee = 0;
  bool isArray = SwigType_isarray(resolved);
  if ((SwigType_ispointer(resolved) && !SwigType_isfunctionpointer(resolved)) || isArray) {
    if (isArray) SwigType_del_array(resolved);
    else SwigType_del_pointer(resolved);
    SwigType *bare = SwigType_strip_qualifiers(resolved);
    int code = SwigType_type(bare);
    if (code == T_VOID || code == T_CHAR || isNumberCode(code) || SwigType_ispointer(bare) || isUnknownUserType(n, bare)) {
      pointee = Copy(resolved);
      // A typedef of an anonymous enum (GDALDataType) cannot be spelled with the enum keyword.
      Replace(pointee, "enum ", "", DOH_REPLACE_ANY);
    }
    Delete(bare);
  }
  Delete(resolved);
  return pointee;
}

// A typedef from a header SWIG never parsed can hide a pointer (spatialite's gaiaGeomCollPtr, GDAL's GDALRasterBandH);
// the policy is a no-op for types that turn out not to be pointers.
static bool mayHidePointer(Node *n, const SwigType *t) {
  SwigType *bare = bareType(t);
  bool result = isUnknownUserType(n, bare);
  Delete(bare);
  return result;
}

// How a parameter or return value crosses to JS where embind's own binding cannot carry it. embind binds neither a
// reference to an incomplete class nor an out parameter: a mutable reference to a number or pointer travels as a
// pointer, a reference to a class this interface does not define as crossbind::JsRef. A C API's pointer to a struct
// this interface does not define goes through crossbind::JsStructPointer, and its typedef SWIG never parsed through
// crossbind::JsArg: both return a handle and take a handle or an instance bound by the header defining the struct. A
// function pointer takes a JS function through crossbind::JsCallback. A pointer to const char is a string: it takes a
// JS string (or a handle) through crossbind::JsCString and comes back as a JS string.
enum ArgumentForm { PLAIN_ARGUMENT, POINTER_ARGUMENT, OUT_REFERENCE_ARGUMENT, REFERENCE_ARGUMENT, HIDDEN_TYPE_ARGUMENT, CALLBACK_ARGUMENT, STRUCT_POINTER_ARGUMENT, CSTRING_ARGUMENT };
static const char *const ARGUMENT_TYPES[] = {"", "JsPointer", "JsPointer", "JsRef", "JsArg", "JsCallback", "JsStructPointer", "JsCString"};
static const char *const ARGUMENT_CONVERSIONS[] = {"", "fromJs", "fromJsRef", "fromJsRef", "fromJsArg", "fromJsCallback", "fromJsStruct", "fromJsCString"};

// C APIs read a `const char *` as a NUL-terminated string and copy it (GDAL, sqlite, PROJ, curl); owned strings and
// byte buffers are `char *` and `unsigned char *`, which stay pointers. A handle still passes where an API keeps the
// pointer.
static bool isConstChar(const SwigType *pointee) {
  if (!SwigType_isconst(pointee)) return false;
  SwigType *bare = SwigType_strip_qualifiers(pointee);
  bool result = Equal(bare, "char");
  Delete(bare);
  return result;
}

// C++ may see a struct from another header complete, yet only a bridge of that header binds it.
static bool isForeignStruct(Node *n, const SwigType *pointee) {
  if (!Swig_storage_isexternc(n)) return false;
  SwigType *bare = SwigType_strip_qualifiers(pointee);
  bool result = SwigType_type(bare) == T_USER && SwigType_issimple(bare) && !Language::classLookup(bare);
  Delete(bare);
  return result;
}

// A C API's pointee keeps the typedef name its declaration uses: resolved, GDAL's `VSIStatBuf *` becomes `stat`, which
// the POSIX function stat hides in C++.
static SwigType *declaredPointee(const SwigType *t, SwigType *resolved) {
  SwigType *declared = Copy(t);
  if (SwigType_isqualifier(declared)) SwigType_del_qualifier(declared);
  bool isPointer = SwigType_ispointer(declared) && !SwigType_isfunctionpointer(declared);
  if (!isPointer && !SwigType_isarray(declared)) {
    Delete(declared);
    return resolved;
  }
  if (isPointer) SwigType_del_pointer(declared);
  else SwigType_del_array(declared);
  Delete(resolved);
  Replace(declared, "enum ", "", DOH_REPLACE_ANY);
  return declared;
}

static ArgumentForm argumentForm(Node *n, const SwigType *t, SwigType **inner) {
  SwigType *pointee = handlePointee(n, t);
  if (pointee) {
    ArgumentForm form = isConstChar(pointee) ? CSTRING_ARGUMENT : isForeignStruct(n, pointee) ? STRUCT_POINTER_ARGUMENT : POINTER_ARGUMENT;
    if (inner) *inner = Swig_storage_isexternc(n) ? declaredPointee(t, pointee) : pointee;
    else Delete(pointee);
    return form;
  }
  bool isFunctionTypedef = false;
  SwigType *qualified = qualifyMemberType(n, t, &isFunctionTypedef);
  SwigType *resolved = SwigType_typedef_resolve_all(qualified);
  Delete(qualified);
  if (SwigType_isqualifier(resolved)) SwigType_del_qualifier(resolved);
  ArgumentForm form = PLAIN_ARGUMENT;
  if (isFunctionTypedef && !SwigType_isreference(resolved) && !SwigType_isrvalue_reference(resolved)) {
    form = HIDDEN_TYPE_ARGUMENT;
  } else if (SwigType_isfunctionpointer(resolved)) {
    form = CALLBACK_ARGUMENT;
  } else if (SwigType_isreference(resolved)) {
    SwigType_del_reference(resolved);
    SwigType *bare = SwigType_strip_qualifiers(resolved);
    int code = SwigType_type(bare);
    // embind hands strings and smart pointers over by value, so a mutable reference to one would bind to a temporary.
    bool isPassedByValueInEmbind = Strncmp(bare, "std::basic_string<", 18) == 0 || Equal(bare, "std::string") || Equal(bare, "std::wstring") || Equal(bare, "std::u16string") || Equal(bare, "std::u32string") || Strncmp(bare, "std::unique_ptr<", 16) == 0 || Strncmp(bare, "std::shared_ptr<", 16) == 0;
    if (!SwigType_isconst(resolved) && (isNumberCode(code) || code == T_CHAR || SwigType_ispointer(bare) || isPassedByValueInEmbind)) form = OUT_REFERENCE_ARGUMENT;
    else if (isUnknownUserType(n, bare)) form = REFERENCE_ARGUMENT;
    Delete(bare);
  } else if (!SwigType_isrvalue_reference(resolved) && Swig_storage_isexternc(n) && mayHidePointer(n, resolved)) {
    form = HIDDEN_TYPE_ARGUMENT;
  }
  if (form != PLAIN_ARGUMENT && inner) {
    *inner = form == HIDDEN_TYPE_ARGUMENT ? SwigType_strip_qualifiers(resolved) : Copy(resolved);
    Replace(*inner, "enum ", "", DOH_REPLACE_ANY);
  }
  Delete(resolved);
  return form;
}

// std::unique_ptr, or a template holding one by value: a container, or PROJ's util::nn<WKTNodePtr>, whose template comes
// from a header SWIG never parsed, so typedef resolution leaves its argument unexpanded. A std::function or
// std::shared_ptr whose signature mentions std::unique_ptr is itself copyable.
static bool holdsUniquePtr(const SwigType *t) {
  SwigType *bare = bareType(t);
  bool result = false;
  if (!SwigType_ispointer(bare) && SwigType_istemplate(bare)) {
    String *prefix = SwigType_templateprefix(bare);
    if (Equal(prefix, "std::unique_ptr")) {
      result = true;
    } else if (!Equal(prefix, "std::function") && !Equal(prefix, "std::shared_ptr")) {
      String *templateArgs = SwigType_templateargs(bare);
      List *args = SwigType_parmlist(templateArgs);
      for (Iterator it = First(args); it.item && !result; it = Next(it)) result = holdsUniquePtr(it.item);
      Delete(args);
      Delete(templateArgs);
    }
    Delete(prefix);
  }
  Delete(bare);
  return result;
}

// embind copies a returned class, which a container of std::unique_ptr or a std::unique_ptr with its own deleter
// (GEOS's GeometryFactory::Ptr) refuses.
static bool returnsMoveOnly(const SwigType *t) {
  SwigType *bare = bareType(t);
  bool result = false;
  if (!SwigType_ispointer(bare) && holdsUniquePtr(bare)) {
    String *prefix = SwigType_istemplate(bare) ? SwigType_templateprefix(bare) : 0;
    String *templateArgs = prefix && Equal(prefix, "std::unique_ptr") ? SwigType_templateargs(bare) : 0;
    List *args = templateArgs ? SwigType_parmlist(templateArgs) : 0;
    result = !args || Len(args) != 1;
    Delete(args);
    Delete(templateArgs);
    Delete(prefix);
  }
  Delete(bare);
  return result;
}

// A reference to a std::unique_ptr (PROJ's `const WKTNodePtr &lookForChild()`) reaches JS as the object it points to,
// which the unique_ptr keeps owning; embind would copy the unique_ptr.
static bool returnsUniquePtrReference(Node *n) {
  SwigType *type = Getattr(n, "type");
  if (!SwigType_isreference(type)) return false;
  SwigType *resolved = SwigType_typedef_resolve_all(type);
  SwigType *bare = bareType(resolved);
  bool result = Strncmp(bare, "std::unique_ptr<", 16) == 0;
  Delete(bare);
  Delete(resolved);
  return result;
}

// embind copies a class returned by reference. An abstract class or one with a deleted copy constructor (PROJ's
// AxisDirection) cannot be copied, and a method returning its own class (a fluent setter such as PROJ's
// PROJStringParser::setUsePROJ4InitRules, whose class holds a std::unique_ptr) means the same object: such a result
// comes back as a pointer instead.
static bool returnsReferenceAsPointer(Node *n) {
  SwigType *type = Getattr(n, "type");
  if (!SwigType_isreference(type)) return false;
  SwigType *bare = bareType(type);
  Node *cls = Language::classLookup(bare);
  Node *owner = parentNode(n);
  if (owner && Equal(nodeType(owner), "extend")) owner = parentNode(owner);
  bool isOwnClass = cls && owner && Equal(nodeType(owner), "class") && Equal(Getattr(cls, "name"), Getattr(owner, "name"));
  bool result = cls && (Getattr(cls, "abstracts") || GetFlag(cls, "allocate:deleted_copy_constructor") || isOwnClass);
  Delete(bare);
  return result;
}

// embind copies a class returned by value. A nested class (GDAL's OGRFieldDefn::TemporaryUnsealer, which SWIG only
// sees declared, or OGRCurve::ConstIterator, whose copy is implicitly deleted) or a class whose copy constructor is
// deleted may not allow that, so crossbind::returned constructs such a result in place.
static bool returnsUncopyableValue(Node *n) {
  SwigType *type = Getattr(n, "type");
  if (SwigType_ispointer(type) || SwigType_isreference(type) || SwigType_isrvalue_reference(type)) return false;
  SwigType *qualified = qualifyMemberType(n, type);
  SwigType *bare = bareType(qualified);
  Delete(qualified);
  bool result = false;
  if (SwigType_type(bare) == T_USER && Strncmp(bare, "std::", 5) != 0) {
    Node *cls = Language::classLookup(bare);
    String *owner = Swig_scopename_prefix(bare);
    result = (owner && Language::classLookup(owner)) || (cls && GetFlag(cls, "allocate:deleted_copy_constructor"));
    Delete(owner);
  }
  Delete(bare);
  return result;
}

// SWIG drops a nested class it cannot wrap (GDAL's OGRCurve::ConstIterator, OGRLayer::FeatureIterator) and leaves its
// name unqualified and unknown, just like a type from another header (GDAL's GDALComputedRasterBand, which only moves).
// Such a value is returned through an adapter and crossbind::returned, which C++ turns into a copy or, for a type that
// cannot be copied, into a handle.
static bool returnsUnknownValue(Node *n) {
  SwigType *type = Getattr(n, "type");
  if (SwigType_ispointer(type) || SwigType_isreference(type) || SwigType_isrvalue_reference(type)) return false;
  SwigType *qualified = qualifyMemberType(n, type);
  SwigType *bare = bareType(qualified);
  Delete(qualified);
  bool result = SwigType_type(bare) == T_USER && Strncmp(bare, "std::", 5) != 0 && !Language::classLookup(bare);
  Delete(bare);
  return result;
}

// A std::vector of a type SWIG does not know (PROJ's std::vector<CRSNNPtr>), returned by value or const reference, goes
// through crossbind::returned: a vector of smart pointer wrappers comes back as a vector of their shared_ptrs, which
// every class registers as Vector<Class>, and any other vector as the copy embind already returns.
static bool returnsVectorOfUnknown(Node *n) {
  SwigType *type = Getattr(n, "type");
  if (SwigType_ispointer(type) || SwigType_isrvalue_reference(type)) return false;
  SwigType *qualified = qualifyMemberType(n, type);
  SwigType *resolved = SwigType_typedef_resolve_all(qualified);
  Delete(qualified);
  bool isReference = SwigType_isreference(resolved);
  if (isReference) SwigType_del_reference(resolved);
  bool isReturnedCopy = !isReference || SwigType_isconst(resolved);
  SwigType *bare = SwigType_strip_qualifiers(resolved);
  Delete(resolved);
  bool result = false;
  if (isReturnedCopy && SwigType_istemplate(bare)) {
    String *prefix = SwigType_templateprefix(bare);
    if (Equal(prefix, "std::vector")) {
      String *templateArgs = SwigType_templateargs(bare);
      List *args = SwigType_parmlist(templateArgs);
      SwigType *element = Len(args) > 0 ? Getitem(args, 0) : 0;
      result = element && SwigType_type(element) == T_USER && Strncmp(element, "std::", 5) != 0 && !Language::classLookup(element);
      Delete(args);
      Delete(templateArgs);
    }
    Delete(prefix);
  }
  Delete(bare);
  return result;
}

// A mutable reference to a number, pointer or string comes back as the copy embind already returns.
static ArgumentForm returnForm(Node *n) {
  ArgumentForm form = argumentForm(n, Getattr(n, "type"), 0);
  return form == OUT_REFERENCE_ARGUMENT ? PLAIN_ARGUMENT : form;
}

static String *returnExpression(Node *n, const String *call) {
  SwigType *type = Getattr(n, "type");
  if (returnsUniquePtrReference(n)) return NewStringf("crossbind::toJs(%s.get())", call);
  if (returnsMoveOnly(type)) return NewStringf(SwigType_isreference(type) ? "crossbind::toJs(&%s)" : "crossbind::movedOut(%s)", call);
  if (returnsReferenceAsPointer(n)) return NewStringf("crossbind::toJs(&%s)", call);
  if (returnsUncopyableValue(n) || returnsVectorOfUnknown(n)) return NewStringf("crossbind::returned([&] { return %s; })", call);
  switch (returnForm(n)) {
  case POINTER_ARGUMENT:
  case CALLBACK_ARGUMENT:
    return NewStringf("crossbind::toJs(%s)", call);
  case REFERENCE_ARGUMENT:
    return NewStringf("crossbind::toJsRef(%s)", call);
  case HIDDEN_TYPE_ARGUMENT:
    return NewStringf("crossbind::toJsArg(%s)", call);
  case STRUCT_POINTER_ARGUMENT:
    return NewStringf("crossbind::toHandle(%s)", call);
  case CSTRING_ARGUMENT:
    return NewStringf("crossbind::toJsCString(%s)", call);
  default:
    return returnsUnknownValue(n) ? NewStringf("crossbind::returned([&] { return %s; })", call) : Copy(call);
  }
}

// embind's base<> downcasts with static_cast, which a virtual base refuses (GDAL's GDALAttribute : virtual public
// GDALAbstractMDArray); crossbind::VirtualBase downcasts with dynamic_cast. The parser lists the bases named virtual.
static bool inheritsVirtually(Node *cls, Node *base) {
  List *virtualBases = Getattr(cls, "virtualbaselist");
  if (!virtualBases) return false;
  String *baseName = Swig_scopename_last(Getattr(base, "name"));
  bool result = false;
  for (Iterator it = First(virtualBases); it.item && !result; it = Next(it)) {
    String *listed = Swig_scopename_last(it.item);
    result = Equal(listed, baseName);
    Delete(listed);
  }
  Delete(baseName);
  return result;
}

static bool usesPointerRuntime = false;
static String *deferredBlocks = 0;

// Bridges of several headers link into one module, and embind stops the module when a type or a public name is
// registered twice: GDAL declares GDALVersionInfo in both gdal.h and ogr_core.h, and PROJ has an enum named Type in three
// classes. Each registration is claimed first, so a repeated one is skipped and the first bridge's registration stands.
static const char *REGISTRATION_RUNTIME =
  "#include <set>\n#include <string>\n#include <typeinfo>\n\n"
  "namespace crossbind {\n"
  "inline bool claimRegistration(const std::string &key) {\n"
  "  static std::set<std::string> claimed;\n"
  "  return claimed.insert(key).second;\n"
  "}\n"
  "inline bool claimType(const std::type_info &type, const char *name) {\n"
  "  return claimRegistration(std::string(\"type \") + type.name()) && claimRegistration(std::string(\"name \") + name);\n"
  "}\n"
  "inline bool claimFunction(const char *name, int arity) {\n"
  "  return claimRegistration(std::string(\"function \") + name + \"/\" + std::to_string(arity));\n"
  "}\n"
  "}\n\n";

// A NativePointer handle is shared_ptr-owned: JS GC or delete() frees the handle, and the storage of cstring and
// allocBuffer handles, never a pointee owned by C++. A handle made from a const pointer is read-only and mutable
// parameters reject it; pointee types must match, and an untyped (void) handle stands in only for an incomplete or
// trivially copyable pointee, so a byte buffer never poses as a std::string. allocBuffer allocates one hidden byte
// more, so readCString stops inside a buffer the C side filled completely. The registration is an inline InitFunc:
// it runs once per JS context (every embind-jsi runtime, every wasm worker) however many bridges include it; the
// type tags and that single registration assume all bridges link into one module. A C++ class that is complete in one
// imported header and incomplete in another still gets two JS representations; a C struct from another header comes
// back as a handle, and a parameter taking one also accepts an instance bound by the header defining it.
// Addresses are kept as integers so function pointers behind typedefs SWIG never parsed round-trip too. A void* slot
// from allocPointer stands in for any T** and remembers T once C code writes through it. Owned buffers carry their
// size, so the read and write helpers stay in bounds, and keep alive the handles written into them. A pointer C
// returns carries no size: reads and writes through it trust the index, as C does. readBytes and writeBytes carry
// one byte per UTF-16 code unit, the only string form both embind runtimes keep byte for byte. A std::string behind
// a pointer is a handle from allocString, read back with readString.
// A JS function passed as a C callback lives in a slot of the thread that passed it: C must call it on that thread
// (JS values cannot cross threads on either runtime), and a released slot goes to the next function passed, so JS
// releases a callback only after C stops calling it.
// A smart pointer wrapper that converts to std::shared_ptr<T> (a non-null type such as gsl::not_null, or PROJ's nn)
// crosses as that shared_ptr: always when returned, and as a const reference parameter when it can be built from one.
// A returned std::vector of such wrappers crosses as a std::vector of those shared_ptrs.
// sharedOf converts implicitly from a const reference, the expression isSharedWrapper tests; a cast is ambiguous for
// nn, whose const & and && conversions each reach a different shared_ptr constructor.
static const char *POINTER_RUNTIME =
  "\n#include <algorithm>\n#include <array>\n#include <cmath>\n#include <cstdint>\n#include <cstdio>\n#include <cstring>\n#include <limits>\n#include <memory>\n#include <optional>\n#include <stdexcept>\n#include <string>\n#include <type_traits>\n#include <utility>\n#include <vector>\n\n"
  "namespace crossbind {\n"
  "template<typename T, typename = void> struct IsComplete : std::false_type {};\n"
  "template<typename T> struct IsComplete<T, std::void_t<decltype(sizeof(T))>> : std::true_type {};\n"
  "template<typename T> struct IsBasicString : std::false_type {};\n"
  "template<typename C, typename Traits, typename Allocator> struct IsBasicString<std::basic_string<C, Traits, Allocator>> : std::true_type {};\n"
  "template<typename Q> constexpr bool isRawPointee = IsComplete<Q>::value && (std::is_class_v<Q> || std::is_union_v<Q>) && !IsBasicString<std::remove_cv_t<Q>>::value;\n"
  "template<typename T> inline const char pointeeTag = 0;\n"
  "struct NativePointer {\n"
  "  std::uintptr_t address;\n"
  "  const char *pointee;\n"
  "  bool readOnly;\n"
  "  std::shared_ptr<void> storage;\n"
  "  size_t capacity = 0;\n"
  "  const char *element = nullptr;\n"
  "  bool elementReadOnly = false;\n"
  "  std::vector<std::shared_ptr<NativePointer>> retained;\n"
  "};\n"
  "using PointerHandle = std::shared_ptr<NativePointer>;\n"
  "template<typename Q> using JsPointer = std::conditional_t<isRawPointee<Q>, Q *, PointerHandle>;\n"
  "template<typename T> void recordElement(NativePointer &p) {\n"
  "  if constexpr (std::is_pointer_v<T>) {\n"
  "    p.element = &pointeeTag<std::remove_cv_t<std::remove_pointer_t<T>>>;\n"
  "    p.elementReadOnly = std::is_const_v<std::remove_pointer_t<T>>;\n"
  "  }\n"
  "}\n"
  "template<typename T> constexpr bool acceptsUntypedMemory = std::disjunction_v<std::negation<IsComplete<T>>, std::is_trivially_copyable<T>>;\n"
  "template<typename Q> Q *fromJs(Q *p) { return p; }\n"
  "template<typename Q> Q *fromJs(const PointerHandle &p) {\n"
  "  if (!p) return nullptr;\n"
  "  if (!std::is_const_v<Q> && p->readOnly) throw std::invalid_argument(\"crossbind: a read-only pointer cannot be passed as a mutable pointer\");\n"
  "  using T = std::remove_cv_t<Q>;\n"
  "  const char *expected = &pointeeTag<T>;\n"
  "  bool slot = std::is_pointer_v<T> && p->pointee == &pointeeTag<void *>;\n"
  "  bool untyped = p->pointee == &pointeeTag<void> && acceptsUntypedMemory<T>;\n"
  "  if (p->pointee != expected && !untyped && expected != &pointeeTag<void> && !slot) throw std::invalid_argument(\"crossbind: pointer type mismatch\");\n"
  "  recordElement<T>(*p);\n"
  "  return reinterpret_cast<Q *>(p->address);\n"
  "}\n"
  "template<typename Q> PointerHandle toHandle(Q *p) {\n"
  "  if (!p) return nullptr;\n"
  "  PointerHandle handle = std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(p), &pointeeTag<std::remove_cv_t<Q>>, std::is_const_v<Q>, nullptr});\n"
  "  recordElement<std::remove_cv_t<Q>>(*handle);\n"
  "  return handle;\n"
  "}\n"
  "template<typename Q> JsPointer<Q> toJs(Q *p) {\n"
  "  if constexpr (isRawPointee<Q>) return p;\n"
  "  else return toHandle(p);\n"
  "}\n"
  "template<typename Q> using JsCString = emscripten::val;\n"
  "struct CStringArg {\n"
  "  bool isText = false;\n"
  "  std::string text;\n"
  "  PointerHandle handle;\n"
  "  const char *pointer = nullptr;\n"
  "  operator const char *() const { return isText ? text.c_str() : pointer; }\n"
  "};\n"
  "template<typename Q> CStringArg fromJsCString(const emscripten::val &value) {\n"
  "  CStringArg arg;\n"
  "  if (value.isNull() || value.isUndefined()) return arg;\n"
  "  if (value.typeOf().as<std::string>() == \"string\") {\n"
  "    arg.isText = true;\n"
  "    arg.text = value.as<std::string>();\n"
  "  } else if (value.instanceof(emscripten::val::module_property(\"NativePointer\"))) {\n"
  "    arg.handle = value.as<PointerHandle>();\n"
  "    arg.pointer = fromJs<const char>(arg.handle);\n"
  "  } else {\n"
  "    throw std::invalid_argument(\"crossbind: a const char* parameter takes a string, a pointer handle or null\");\n"
  "  }\n"
  "  return arg;\n"
  "}\n"
  "inline emscripten::val toJsCString(const char *text) { return text ? emscripten::val(std::string(text)) : emscripten::val::null(); }\n"
  "template<typename Q> using JsStructPointer = std::conditional_t<isRawPointee<Q>, emscripten::val, PointerHandle>;\n"
  "template<typename Q> Q *fromJsStruct(const PointerHandle &p) { return fromJs<Q>(p); }\n"
  "template<typename Q> Q *fromJsStruct(const emscripten::val &value) {\n"
  "  if (value.isNull() || value.isUndefined()) return nullptr;\n"
  "  if (value.instanceof(emscripten::val::module_property(\"NativePointer\"))) return fromJs<Q>(value.as<PointerHandle>());\n"
  "  return value.as<Q *>(emscripten::allow_raw_pointers());\n"
  "}\n"
  "template<typename T> constexpr bool isFunctionPointer = std::is_pointer_v<T> && std::is_function_v<std::remove_pointer_t<T>>;\n"
  "template<typename F> using JsCallback = emscripten::val;\n"
  "inline constexpr size_t callbackSlotCount = 64;\n"
  "inline std::array<std::optional<emscripten::val>, callbackSlotCount> &callbackSlots() {\n"
  "  thread_local std::array<std::optional<emscripten::val>, callbackSlotCount> slots;\n"
  "  return slots;\n"
  "}\n"
  "template<typename A> auto callbackArgument(std::remove_reference_t<A> &value) {\n"
  "  using U = std::remove_cv_t<std::remove_reference_t<A>>;\n"
  "  if constexpr (std::is_same_v<U, const char *>) return toJsCString(value);\n"
  "  else if constexpr (std::is_pointer_v<U>) return toHandle(value);\n"
  "  else if constexpr (std::is_enum_v<U>) return static_cast<std::underlying_type_t<U>>(value);\n"
  "  else if constexpr (std::is_class_v<U> || std::is_union_v<U>) return toHandle(&value);\n"
  "  else return U(value);\n"
  "}\n"
  "template<typename R, typename... A> R invokeCallback(size_t slot, A... args) {\n"
  "  std::optional<emscripten::val> &function = callbackSlots()[slot];\n"
  "  if (!function) {\n"
  "    std::fprintf(stderr, \"crossbind: C called a callback that JS released, or called it from another thread than the one that passed it\\n\");\n"
  "    return R();\n"
  "  }\n"
  "  emscripten::val result = (*function)(callbackArgument<A>(args)...);\n"
  "  if constexpr (std::is_void_v<R>) return;\n"
  "  else if constexpr (std::is_pointer_v<R>) return result.isNull() || result.isUndefined() ? nullptr : fromJs<std::remove_pointer_t<R>>(result.as<PointerHandle>());\n"
  "  else if constexpr (std::is_enum_v<R>) return static_cast<R>(result.as<std::underlying_type_t<R>>());\n"
  "  else return result.as<R>();\n"
  "}\n"
  "template<typename F> struct Callback { static constexpr bool isSupported = false; };\n"
  "template<typename R, typename... A> struct Callback<R (*)(A...)> {\n"
  "  static constexpr bool isSupported = true;\n"
  "  template<size_t I> static R call(A... args) { return invokeCallback<R, A...>(I, std::forward<A>(args)...); }\n"
  "};\n"
  "template<typename F, size_t... I> constexpr std::array<F, sizeof...(I)> callbackTable(std::index_sequence<I...>) { return {{&Callback<F>::template call<I>...}}; }\n"
  "template<typename F> inline constexpr std::array<F, callbackSlotCount> trampolines = callbackTable<F>(std::make_index_sequence<callbackSlotCount>());\n"
  "inline size_t claimCallbackSlot(const emscripten::val &function) {\n"
  "  std::array<std::optional<emscripten::val>, callbackSlotCount> &slots = callbackSlots();\n"
  "  for (size_t i = 0; i < callbackSlotCount; ++i) {\n"
  "    if (slots[i] && slots[i]->strictlyEquals(function)) return i;\n"
  "  }\n"
  "  for (size_t i = 0; i < callbackSlotCount; ++i) {\n"
  "    if (!slots[i]) {\n"
  "      slots[i] = function;\n"
  "      return i;\n"
  "    }\n"
  "  }\n"
  "  throw std::length_error(\"crossbind: every callback slot holds a function; releaseCallback frees the ones C no longer calls\");\n"
  "}\n"
  "template<typename F> F fromJsCallback(const emscripten::val &value) {\n"
  "  if (value.isNull() || value.isUndefined()) return nullptr;\n"
  "  if (value.typeOf().as<std::string>() != \"function\") return fromJs<std::remove_pointer_t<F>>(value.as<PointerHandle>());\n"
  "  if constexpr (Callback<F>::isSupported) return trampolines<F>[claimCallbackSlot(value)];\n"
  "  else throw std::invalid_argument(\"crossbind: a JS function cannot stand in for a variadic C callback\");\n"
  "}\n"
  "inline bool releaseCallback(const emscripten::val &function) {\n"
  "  for (std::optional<emscripten::val> &slot : callbackSlots()) {\n"
  "    if (slot && slot->strictlyEquals(function)) {\n"
  "      slot.reset();\n"
  "      return true;\n"
  "    }\n"
  "  }\n"
  "  return false;\n"
  "}\n"
  "template<typename T> constexpr bool isPassedByAddress = !IsComplete<T>::value || std::is_class_v<T> || std::is_union_v<T>;\n"
  "template<typename T> struct IsSharedPtr : std::false_type {};\n"
  "template<typename T> struct IsSharedPtr<std::shared_ptr<T>> : std::true_type {};\n"
  "template<typename W, typename = void> struct Dereferenced {};\n"
  "template<typename W> struct Dereferenced<W, std::void_t<decltype(*std::declval<const W &>())>> {\n"
  "  using type = std::remove_cv_t<std::remove_reference_t<decltype(*std::declval<const W &>())>>;\n"
  "};\n"
  "template<typename W, bool = IsComplete<W>::value && std::is_class_v<W>> struct WrapperPointee {};\n"
  "template<typename W> struct WrapperPointee<W, true> : Dereferenced<W> {};\n"
  "template<typename W, typename = void> constexpr bool isSharedWrapper = false;\n"
  "template<typename W> constexpr bool isSharedWrapper<W, std::void_t<typename WrapperPointee<W>::type>> = !IsSharedPtr<W>::value && std::is_convertible_v<const W &, std::shared_ptr<typename WrapperPointee<W>::type>>;\n"
  "template<typename W> using SharedOf = std::shared_ptr<typename WrapperPointee<W>::type>;\n"
  "template<typename W> SharedOf<W> sharedOf(const W &wrapper) { return wrapper; }\n"
  "template<typename V> constexpr bool isSharedWrapperVector = false;\n"
  "template<typename T, typename A> constexpr bool isSharedWrapperVector<std::vector<T, A>> = isSharedWrapper<T>;\n"
  "template<typename V> std::vector<SharedOf<typename V::value_type>> sharedVector(const V &values) {\n"
  "  std::vector<SharedOf<typename V::value_type>> shared;\n"
  "  shared.reserve(values.size());\n"
  "  for (const auto &value : values) shared.push_back(sharedOf(value));\n"
  "  return shared;\n"
  "}\n"
  "template<typename Q, typename = void> struct JsRefOf { using type = std::conditional_t<isPassedByAddress<std::remove_cv_t<Q>>, JsPointer<Q>, std::remove_cv_t<Q>>; };\n"
  "template<typename Q> struct JsRefOf<Q, std::enable_if_t<std::is_const_v<Q> && isSharedWrapper<std::remove_cv_t<Q>> && std::is_constructible_v<std::remove_cv_t<Q>, const SharedOf<std::remove_cv_t<Q>> &>>> { using type = SharedOf<std::remove_cv_t<Q>>; };\n"
  "template<typename Q> using JsRef = typename JsRefOf<Q>::type;\n"
  "template<typename T> using JsArg = std::conditional_t<isFunctionPointer<T>, JsCallback<T>, std::conditional_t<std::is_pointer_v<T>, JsStructPointer<std::remove_pointer_t<T>>, T>>;\n"
  "template<typename Q> Q &fromJsRef(Q *p) {\n"
  "  if (!p) throw std::invalid_argument(\"crossbind: a null pointer cannot be passed as a reference\");\n"
  "  return *p;\n"
  "}\n"
  "template<typename Q> Q &fromJsRef(const PointerHandle &p) { return fromJsRef<Q>(fromJs<Q>(p)); }\n"
  "template<typename Q> Q &fromJsRef(std::remove_cv_t<Q> &value) { return value; }\n"
  "template<typename Q> std::remove_cv_t<Q> fromJsRef(const SharedOf<std::remove_cv_t<Q>> &p) {\n"
  "  if (!p) throw std::invalid_argument(\"crossbind: a null pointer cannot be passed where a non-null pointer is required\");\n"
  "  return std::remove_cv_t<Q>(p);\n"
  "}\n"
  "template<typename T> T fromJsArg(JsArg<T> value) {\n"
  "  if constexpr (isFunctionPointer<T>) return fromJsCallback<T>(value);\n"
  "  else if constexpr (std::is_pointer_v<T>) return fromJsStruct<std::remove_pointer_t<T>>(value);\n"
  "  else return value;\n"
  "}\n"
  "template<typename Q> auto toJsRef(Q &ref) {\n"
  "  if constexpr (isSharedWrapper<std::remove_cv_t<Q>>) return sharedOf(ref);\n"
  "  else if constexpr (isPassedByAddress<std::remove_cv_t<Q>>) return toJs(&ref);\n"
  "  else return std::remove_cv_t<Q>(ref);\n"
  "}\n"
  "template<typename T> auto toJsArg(T value) {\n"
  "  if constexpr (std::is_pointer_v<T>) return toHandle(value);\n"
  "  else return value;\n"
  "}\n"
  "template<typename T, typename D> std::shared_ptr<T> movedOut(std::unique_ptr<T, D> &&value) { return std::shared_ptr<T>(std::move(value)); }\n"
  "template<typename R> PointerHandle movedOut(R &&value) {\n"
  "  auto owned = std::make_shared<std::decay_t<R>>(std::forward<R>(value));\n"
  "  return std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(owned.get()), &pointeeTag<std::decay_t<R>>, false, owned});\n"
  "}\n"
  "template<typename B> struct VirtualBase : emscripten::base<B> {\n"
  "  template<typename C> static C *downcast(B *p) {\n"
  "    if constexpr (std::is_polymorphic_v<B>) return dynamic_cast<C *>(p);\n"
  "    else return nullptr;\n"
  "  }\n"
  "  template<typename C> static C *(*getDowncaster())(B *) { return &downcast<C>; }\n"
  "};\n"
  "template<typename F> auto returned(F &&call) {\n"
  "  using R = std::invoke_result_t<F &>;\n"
  "  if constexpr (isSharedWrapper<R>) {\n"
  "    return sharedOf(call());\n"
  "  } else if constexpr (isSharedWrapperVector<R>) {\n"
  "    return sharedVector(call());\n"
  "  } else if constexpr (std::is_class_v<R> && !std::is_copy_constructible_v<R>) {\n"
  "    std::shared_ptr<R> owned(new R(call()));\n"
  "    return std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(owned.get()), &pointeeTag<R>, false, owned});\n"
  "  } else {\n"
  "    return call();\n"
  "  }\n"
  "}\n"
  "inline PointerHandle ownedBytes(size_t capacity, const char *pointee) {\n"
  "  std::shared_ptr<char[]> bytes(new char[capacity + 1]());\n"
  "  PointerHandle p = std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(bytes.get()), pointee, false, bytes});\n"
  "  p->capacity = capacity;\n"
  "  return p;\n"
  "}\n"
  "inline size_t checkedSize(int value, const char *helper) {\n"
  "  if (value < 0) throw std::invalid_argument(std::string(\"crossbind: \") + helper + \" needs a non-negative size\");\n"
  "  return static_cast<size_t>(value);\n"
  "}\n"
  "inline size_t checkedOffset(const PointerHandle &p, const char *helper, size_t index, size_t size) {\n"
  "  if (!p) throw std::invalid_argument(std::string(\"crossbind: \") + helper + \" got a null pointer\");\n"
  "  bool overflows = size != 0 && index >= std::numeric_limits<size_t>::max() / size;\n"
  "  if (overflows || (p->storage && (index + 1) * size > p->capacity)) throw std::out_of_range(std::string(\"crossbind: \") + helper + \" is out of bounds\");\n"
  "  return index * size;\n"
  "}\n"
  "inline void checkWritable(const PointerHandle &p, const char *helper) {\n"
  "  if (p->readOnly) throw std::invalid_argument(std::string(\"crossbind: \") + helper + \" got a read-only pointer\");\n"
  "}\n"
  "inline PointerHandle cstring(const std::string &text) {\n"
  "  PointerHandle p = ownedBytes(text.size() + 1, &pointeeTag<char>);\n"
  "  std::memcpy(reinterpret_cast<char *>(p->address), text.data(), text.size());\n"
  "  return p;\n"
  "}\n"
  "inline PointerHandle allocBuffer(int size) { return ownedBytes(checkedSize(size, \"allocBuffer\"), &pointeeTag<void>); }\n"
  "inline PointerHandle allocPointer(int count) {\n"
  "  size_t slots = checkedSize(count, \"allocPointer\");\n"
  "  if (slots > (std::numeric_limits<size_t>::max() - 1) / sizeof(void *)) throw std::out_of_range(\"crossbind: allocPointer got more slots than memory can address\");\n"
  "  return ownedBytes(slots * sizeof(void *), &pointeeTag<void *>);\n"
  "}\n"
  "inline std::string readCString(PointerHandle p) {\n"
  "  if (!p) throw std::invalid_argument(\"crossbind: readCString got a null pointer\");\n"
  "  if (p->pointee != &pointeeTag<char> && p->pointee != &pointeeTag<signed char> && p->pointee != &pointeeTag<unsigned char> && p->pointee != &pointeeTag<void>) throw std::invalid_argument(\"crossbind: pointer type mismatch\");\n"
  "  return reinterpret_cast<const char *>(p->address);\n"
  "}\n"
  "inline PointerHandle allocString(const std::string &text) { return movedOut(std::string(text)); }\n"
  "inline std::string readString(PointerHandle p) {\n"
  "  if (!p) throw std::invalid_argument(\"crossbind: readString got a null pointer\");\n"
  "  if (p->pointee != &pointeeTag<std::string>) throw std::invalid_argument(\"crossbind: pointer type mismatch\");\n"
  "  return *reinterpret_cast<const std::string *>(p->address);\n"
  "}\n"
  "inline PointerHandle readPointerAt(PointerHandle slots, int index) {\n"
  "  size_t at = checkedOffset(slots, \"readPointerAt\", checkedSize(index, \"readPointerAt\"), sizeof(void *));\n"
  "  void *value = nullptr;\n"
  "  std::memcpy(&value, reinterpret_cast<const char *>(slots->address) + at, sizeof(void *));\n"
  "  if (!value) return nullptr;\n"
  "  return std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(value), slots->element ? slots->element : &pointeeTag<void>, slots->elementReadOnly, nullptr});\n"
  "}\n"
  "inline void writePointerAt(PointerHandle slots, int index, PointerHandle value) {\n"
  "  size_t slot = checkedSize(index, \"writePointerAt\");\n"
  "  size_t at = checkedOffset(slots, \"writePointerAt\", slot, sizeof(void *));\n"
  "  checkWritable(slots, \"writePointerAt\");\n"
  "  void *address = value ? reinterpret_cast<void *>(value->address) : nullptr;\n"
  "  std::memcpy(reinterpret_cast<char *>(slots->address) + at, &address, sizeof(void *));\n"
  "  if (slots->storage) {\n"
  "    if (slot >= slots->retained.size()) slots->retained.resize(slot + 1);\n"
  "    slots->retained[slot] = value;\n"
  "  }\n"
  "  if (value && !slots->element) {\n"
  "    slots->element = value->pointee;\n"
  "    slots->elementReadOnly = value->readOnly;\n"
  "  }\n"
  "}\n"
  "inline size_t numberSize(const std::string &kind) {\n"
  "  if (kind == \"int8\" || kind == \"uint8\") return 1;\n"
  "  if (kind == \"int16\" || kind == \"uint16\") return 2;\n"
  "  if (kind == \"int32\" || kind == \"uint32\" || kind == \"float32\") return 4;\n"
  "  if (kind == \"int64\" || kind == \"uint64\" || kind == \"float64\") return 8;\n"
  "  throw std::invalid_argument(\"crossbind: unknown number kind \" + kind);\n"
  "}\n"
  "template<typename T> double readAs(const char *at) {\n"
  "  T value;\n"
  "  std::memcpy(&value, at, sizeof(T));\n"
  "  return static_cast<double>(value);\n"
  "}\n"
  "template<typename T> void writeAs(char *at, double number) {\n"
  "  bool fits = std::is_integral_v<T> ? (number >= static_cast<double>(std::numeric_limits<T>::lowest()) && number < static_cast<double>(std::numeric_limits<T>::max()) + 1.0) : (!std::isfinite(number) || std::fabs(number) <= static_cast<double>(std::numeric_limits<T>::max()));\n"
  "  if (!fits) throw std::out_of_range(\"crossbind: writeNumberAt got a value its kind cannot hold\");\n"
  "  T value = static_cast<T>(number);\n"
  "  std::memcpy(at, &value, sizeof(T));\n"
  "}\n"
  "inline double readNumberAt(PointerHandle p, int index, const std::string &kind) {\n"
  "  size_t size = numberSize(kind);\n"
  "  size_t at = checkedOffset(p, \"readNumberAt\", checkedSize(index, \"readNumberAt\"), size);\n"
  "  const char *bytes = reinterpret_cast<const char *>(p->address) + at;\n"
  "  if (kind == \"int8\") return readAs<int8_t>(bytes);\n"
  "  if (kind == \"uint8\") return readAs<uint8_t>(bytes);\n"
  "  if (kind == \"int16\") return readAs<int16_t>(bytes);\n"
  "  if (kind == \"uint16\") return readAs<uint16_t>(bytes);\n"
  "  if (kind == \"int32\") return readAs<int32_t>(bytes);\n"
  "  if (kind == \"uint32\") return readAs<uint32_t>(bytes);\n"
  "  if (kind == \"int64\") return readAs<int64_t>(bytes);\n"
  "  if (kind == \"uint64\") return readAs<uint64_t>(bytes);\n"
  "  if (kind == \"float32\") return readAs<float>(bytes);\n"
  "  return readAs<double>(bytes);\n"
  "}\n"
  "inline void writeNumberAt(PointerHandle p, int index, const std::string &kind, double number) {\n"
  "  size_t size = numberSize(kind);\n"
  "  size_t at = checkedOffset(p, \"writeNumberAt\", checkedSize(index, \"writeNumberAt\"), size);\n"
  "  checkWritable(p, \"writeNumberAt\");\n"
  "  char *bytes = reinterpret_cast<char *>(p->address) + at;\n"
  "  if (kind == \"int8\") writeAs<int8_t>(bytes, number);\n"
  "  else if (kind == \"uint8\") writeAs<uint8_t>(bytes, number);\n"
  "  else if (kind == \"int16\") writeAs<int16_t>(bytes, number);\n"
  "  else if (kind == \"uint16\") writeAs<uint16_t>(bytes, number);\n"
  "  else if (kind == \"int32\") writeAs<int32_t>(bytes, number);\n"
  "  else if (kind == \"uint32\") writeAs<uint32_t>(bytes, number);\n"
  "  else if (kind == \"int64\") writeAs<int64_t>(bytes, number);\n"
  "  else if (kind == \"uint64\") writeAs<uint64_t>(bytes, number);\n"
  "  else if (kind == \"float32\") writeAs<float>(bytes, number);\n"
  "  else writeAs<double>(bytes, number);\n"
  "}\n"
  "inline std::u16string readBytes(PointerHandle p, int length) {\n"
  "  size_t size = checkedSize(length, \"readBytes\");\n"
  "  checkedOffset(p, \"readBytes\", 0, size);\n"
  "  const unsigned char *bytes = reinterpret_cast<const unsigned char *>(p->address);\n"
  "  return std::u16string(bytes, bytes + size);\n"
  "}\n"
  "inline void writeBytes(PointerHandle p, const std::u16string &bytes) {\n"
  "  checkedOffset(p, \"writeBytes\", 0, bytes.size());\n"
  "  checkWritable(p, \"writeBytes\");\n"
  "  for (char16_t unit : bytes) {\n"
  "    if (unit > 0xFF) throw std::invalid_argument(\"crossbind: writeBytes takes one byte per character\");\n"
  "  }\n"
  "  std::copy(bytes.begin(), bytes.end(), reinterpret_cast<unsigned char *>(p->address));\n"
  "}\n"
  "inline void registerPointerRuntime() {\n"
  "  emscripten::class_<NativePointer>(\"NativePointer\").smart_ptr<PointerHandle>(\"NativePointer\");\n"
  "  emscripten::function(\"cstring\", &cstring);\n"
  "  emscripten::function(\"allocBuffer\", &allocBuffer);\n"
  "  emscripten::function(\"allocPointer\", &allocPointer);\n"
  "  emscripten::function(\"readCString\", &readCString);\n"
  "  emscripten::function(\"readPointerAt\", &readPointerAt);\n"
  "  emscripten::function(\"writePointerAt\", &writePointerAt);\n"
  "  emscripten::function(\"readNumberAt\", &readNumberAt);\n"
  "  emscripten::function(\"writeNumberAt\", &writeNumberAt);\n"
  "  emscripten::function(\"readBytes\", &readBytes);\n"
  "  emscripten::function(\"writeBytes\", &writeBytes);\n"
  "  emscripten::function(\"releaseCallback\", &releaseCallback);\n"
  "  emscripten::function(\"allocString\", &allocString);\n"
  "  emscripten::function(\"readString\", &readString);\n"
  "}\n"
  "inline emscripten::internal::InitFunc pointerRuntimeInit(registerPointerRuntime);\n"
  "}\n";

// The adapter owns a by-value class argument, so it can move it on, which a move-only type such as std::unique_ptr needs.
static bool passesClassByValue(const SwigType *t) {
  if (SwigType_isreference(t) || SwigType_isrvalue_reference(t)) return false;
  SwigType *resolved = SwigType_typedef_resolve_all(t);
  SwigType *bare = SwigType_strip_qualifiers(resolved);
  bool result = SwigType_type(bare) == T_USER;
  Delete(bare);
  Delete(resolved);
  return result;
}

// embind registers no char* type and cannot hold incomplete types: the adapter speaks crossbind::JsPointer to JS.
// Kept on one line so bridgeAsyncGuard can wrap a _JSPI registration in #ifdef.
static String *bindingAdapter(Node *n, ParmList *parms, const_String_or_char_ptr callee, const String *scope) {
  String *decls = NewString("");
  String *args = NewString("");
  int argnum = 0;
  for (Parm *p = parms; p; p = nextSibling(p)) {
    SwigType *pType = Getattr(p, "type");
    if (Strcmp(pType, "void") == 0) continue;
    if (Len(decls) != 0) Append(decls, ", ");
    if (GetFlag(p, "self")) {
      Printf(decls, "%s", SwigType_str(pType, "self"));
      continue;
    }
    String *arg = NewStringf("arg%d", argnum++);
    if (Len(args) != 0) Append(args, ", ");
    SwigType *inner = 0;
    ArgumentForm form = argumentForm(n, pType, &inner);
    if (form != PLAIN_ARGUMENT) {
      SwigType *spelledInner = withoutMemberAliases(inner, scope);
      String *innerType = SwigType_str(spelledInner, 0);
      Printf(decls, "crossbind::%s<%s> %s", ARGUMENT_TYPES[form], innerType, arg);
      Printf(args, "crossbind::%s<%s>(%s)", ARGUMENT_CONVERSIONS[form], innerType, arg);
      usesPointerRuntime = true;
      Delete(innerType);
      Delete(spelledInner);
      Delete(inner);
    } else {
      SwigType *spelled = withoutMemberAliases(pType, scope);
      Printf(decls, "%s", SwigType_str(spelled, arg));
      if (SwigType_isrvalue_reference(pType) || passesClassByValue(pType)) Printf(args, "std::move(%s)", arg);
      else Append(args, arg);
      Delete(spelled);
    }
    Delete(arg);
  }
  String *call = NewStringf("%s(%s)", callee, args);
  String *returned = Equal(nodeType(n), "constructor") ? Copy(call) : returnExpression(n, call);
  if (!Equal(returned, call)) usesPointerRuntime = true;
  String *adapter = NewStringf("emscripten::optional_override([](%s) { return %s; })", decls, returned);
  Delete(returned);
  Delete(call);
  Delete(decls);
  Delete(args);
  return adapter;
}

static Hash *boundOverloads = 0;

static int bindingArity(ParmList *parms) {
  int arity = 0;
  for (Parm *p = parms; p; p = nextSibling(p)) {
    if (!GetFlag(p, "self") && Strcmp(Getattr(p, "type"), "void") != 0) arity++;
  }
  return arity;
}

// embind and embind-jsi both pick an overload by argument count alone, and a second registration with the same count
// throws while the module starts, so only the first overload of each count is bound.
static bool claimOverload(Node *n, const char *kind, const_String_or_char_ptr scope, const String *jsName, ParmList *parms) {
  if (!boundOverloads) boundOverloads = NewHash();
  int arity = bindingArity(parms);
  String *key = NewStringf("%s %s %s %d", kind, scope, jsName, arity);
  bool claimed = !Getattr(boundOverloads, key);
  if (claimed) Setattr(boundOverloads, key, "1");
  else Swig_warning(WARN_LANG_OVERLOAD_IGNORED, Getfile(n), Getline(n), "embind cannot bind another overload of %s taking %d arguments, ignored.\n", jsName, arity);
  Delete(key);
  return claimed;
}

class EMBIND:public Language {
public:
  File *f_begin;
  File *f_exports;
  File *f_runtime;
  File *f_cxx_header;
  File *f_cxx_wrapper;
  File *f_cxx_functions;

  String *exports;
  String *module;
  virtual void main(int argc, char *argv[]);
  virtual int top(Node *n);
  virtual int functionWrapper(Node *n);
  virtual int variableWrapper(Node *n);
  virtual int constantWrapper(Node *n);
  //  virtual int classDeclaration(Node *n);
  virtual int enumDeclaration(Node *n);
  virtual int typedefHandler(Node *n);

  //c++ specific code
  virtual int constructorHandler(Node *n);
  virtual int destructorHandler(Node *n);
  virtual int memberfunctionHandler(Node *n);
  virtual int membervariableHandler(Node *n);
  virtual int classHandler(Node *n);

private:

};

void EMBIND::main(int argc, char *argv[]) {
  int i;

  Preprocessor_define("SWIGEMBIND 1", 0);
  SWIG_library_directory("embind");
  SWIG_config_file("embind.swg");

  allow_overloading();
}

int EMBIND::top(Node *n) {
  module = Getattr(n, "name");

  String *cxx_filename = Getattr(n, "outfile");
  String *cxx_exports_filename = NewString(cxx_filename);
  Printf(cxx_exports_filename, ".exports.json");

  f_begin = NewFile(cxx_filename, "w", SWIG_output_files());
  f_exports = NewFile(cxx_exports_filename, "w", SWIG_output_files());
  if (!f_begin) {
    Printf(stderr, "Unable to open %s for writing\n", cxx_filename);
    Exit(EXIT_FAILURE);
  }
  if (!f_exports) {
    Printf(stderr, "Unable to open %s for writing\n", cxx_exports_filename);
    Exit(EXIT_FAILURE);
  }

  f_runtime = NewString("");
  f_cxx_header = NewString("");
  f_cxx_wrapper = NewString("");
  f_cxx_functions = NewString("");
  exports = NewString("");
  usesPointerRuntime = false;
  deferredBlocks = NewString("");
  boundOverloads = NewHash();

  Printf(exports, "[");
  Printf(f_cxx_header, "#include <emscripten/bind.h>\n%s", REGISTRATION_RUNTIME);

  Swig_register_filebyname("header", f_cxx_header);
  Swig_register_filebyname("wrapper", f_cxx_wrapper);
  Swig_register_filebyname("begin", f_begin);
  Swig_register_filebyname("runtime", f_runtime);

  Swig_banner(f_begin);

  Language::top(n);

  Printf(f_cxx_wrapper, "EMSCRIPTEN_BINDINGS(Functions_%s) {\n", module);
  Printf(f_cxx_wrapper, "%s", f_cxx_functions);
  Printf(f_cxx_wrapper, "}\n");
  if (usesPointerRuntime) {
    Printf(f_cxx_header, "%s", POINTER_RUNTIME);
    Printf(exports, ", \"NativePointer\", \"cstring\", \"allocBuffer\", \"allocPointer\", \"readCString\", \"readPointerAt\", \"writePointerAt\", \"readNumberAt\", \"writeNumberAt\", \"readBytes\", \"writeBytes\", \"releaseCallback\", \"allocString\", \"readString\"");
  }

  Printf(exports, "]\n");
  Replace(exports, ", ", "", DOH_REPLACE_FIRST);

  Dump(exports, f_exports);
  Dump(f_cxx_header, f_runtime);
  Dump(f_cxx_wrapper, f_runtime);
  Dump(f_runtime, f_begin);
  Delete(f_runtime);
  Delete(f_begin);
  Delete(f_cxx_header);
  Delete(f_cxx_wrapper);
  Delete(f_cxx_functions);
  Delete(exports);
  Delete(f_exports);

  return SWIG_OK;
}

int EMBIND::classHandler(Node *n) {
  String *name = Getattr(n, "sym:name");
  String *nsname = Getattr(n, "name");
  String *kind = Getattr(n, "kind");
  String *bases = Getattr(n, "bases");
  String *classType = Getattr(n, "classtype");

  bool isListener = Len(name) > 8 && std::string(Char(name)).substr(Len(name) - 8) == "Listener";

  if (std::string(Char(classType)).substr(0, 12) == "std::vector<") {
    String *params = NewString(std::string(Char(classType)).substr(5).c_str());
    Printf(f_cxx_wrapper, "EMSCRIPTEN_BINDINGS(%s) {\n  if (crossbind::claimType(typeid(std::%s), \"%s\")) emscripten::register_%s(\"%s\");\n}\n\n", name, params, name, params, name);
    Printf(exports, ", \"%s\"", name);
    
  } else if (std::string(Char(classType)).substr(0, 9) == "std::map<") {
    String *params = NewString(std::string(Char(classType)).substr(5).c_str());
    Printf(f_cxx_wrapper, "EMSCRIPTEN_BINDINGS(%s) {\n  if (crossbind::claimType(typeid(std::%s), \"%s\")) emscripten::register_%s(\"%s\");\n}\n\n", name, params, name, params, name);
    Printf(exports, ", \"%s\"", name);
  } else {
    if (isListener) {
      String *className = NewString(name);
      String *listenerHeader = NewString("");
      String *listenerBody = NewString("");
      String *listenerCall = NewString("");
      Printf(listenerHeader, "#include <emscripten/threading.h>\n#include <emscripten/proxying.h>\n\ntypedef union em_variant_val { int i; int64_t i64; float f; double d; void *vp; char *cp; } em_variant_val;\n#define EM_QUEUED_CALL_MAX_ARGS 11\ntypedef struct em_queued_call { int functionEnum; void *functionPtr; _Atomic uint32_t operationDone; em_variant_val args[EM_QUEUED_JS_CALL_MAX_ARGS]; em_variant_val returnValue; void *satelliteData; int calleeDelete; } em_queued_call;\n");
      Printf(listenerHeader, "\nclass EmRunOnMainThread {\npublic:\n");
      Printf(listenerCall, "struct %sWrapper : public emscripten::wrapper<%s> {\n  EMSCRIPTEN_WRAPPER(%sWrapper);\n", name, nsname, name);
      
      for (Node *c = firstChild(n); c; c = nextSibling(c)) {
        String *returnType = Getattr(c, "type");
        Replace(returnType, "(", "", DOH_REPLACE_ANY);
        Replace(returnType, ")", "", DOH_REPLACE_ANY);
        
        String *name = Getattr(c, "name");
        if (returnType) {
          String *params = NewString("");
          String *variables = NewString("");
          String *variables2 = NewString("");
          String *variables3 = NewString("");
          ParmList *pl = Getattr(c, "parms");
          int argnum = 0;
          for (Parm *p = pl; p; p = nextSibling(p), argnum++) {
            String *pName = Getattr(p, "name");
            String *pTypeSplit = Split(Getattr(p, "type"), '.', -1);
            String *pType = Getitem(pTypeSplit, Len(pTypeSplit) - 1);
            Replace(pType, "(", "", DOH_REPLACE_ANY);
            Replace(pType, ")", "", DOH_REPLACE_ANY);
            String *pTypeAll = NewString("");
            String *pTypeAll2 = NewString("");
            if (Len(pTypeSplit) > 1 && Strcmp(Getitem(pTypeSplit, Len(pTypeSplit) - 2), "q(const)") == 0) {
              Printf(pTypeAll, "const %s& %s", pType, pName);
              Printf(pTypeAll2, "const %s", pType);
            } else {
              Printf(pTypeAll, "%s %s", pType, pName);
              Printf(pTypeAll2, "%s", pType);
            }

            if (argnum == 0) {
              Printf(params, "%s", pTypeAll);
            } else {
              Printf(params, ", %s", pTypeAll);
            }
            Printf(variables, ", %s", pName);
            Printf(variables2, "    call.args[%d].vp = (void *)&%s;\n", argnum + 1, pName);
            Printf(variables3, "    %s %s = *((%s*) q->args[%d].vp);\n", pTypeAll2, pName, pTypeAll2, argnum + 1);
            // Printf(f_cxx_wrapper, "%s\n", p);
          }

          String *returnBody = NewString("");
          String *returnCall = NewString("");
          String *returnCallEnd = NewString("");
          Printf(listenerHeader, "  static void %s (void* arg);\n", name);
          if (Strcmp(returnType, "void") != 0) {
            Printf(listenerHeader, "  struct Return%s {\n    Return%s(%s value) {\n      this->value = std::move(value);\n    }\n    %s value;\n  };\n  struct Return%sContainer {\n    std::shared_ptr<Return%s> value;\n  };\n", name, name, returnType, returnType, name, name );
            Printf(returnBody, "    Return%sContainer r = *((Return%sContainer*) q->returnValue.vp);\n    r.value = std::shared_ptr<Return%s>(new Return%s(self->call<%s>(\"%s\"%s)));\n", name, name, name, name, returnType, name, variables);
            Printf(returnCall, "    EmRunOnMainThread::Return%sContainer r;\n    call.returnValue.vp = (void *)&r;\n", name);
            Printf(returnCallEnd, "    return r.value->value;\n");
          } else {
            Printf(returnBody, "    self->call<void>(\"%s\"%s);\n", name, variables);
          }
          // Printf(listenerCall, "  %s %s(%s) { return call<%s>(\"%s\"%s); }\n", returnType, name, params, returnType, name, variables);
          Printf(listenerCall, "  %s %s(%s) {\n    em_queued_call call = {EM_FUNC_SIG_V};\n%s\n    call.args[0].vp = (void *)this;\n%s\n    if (pthread_equal(emscripten_main_browser_thread_id(), pthread_self())) {\n      EmRunOnMainThread::%s(&call);\n    } else {\n      emscripten_proxy_async(emscripten_proxy_get_system_queue(), emscripten_main_browser_thread_id(), EmRunOnMainThread::%s, &call);\n      emscripten_wait_for_call_v(&call, INFINITY);\n    }\n%s  }\n\n", returnType, name, params, returnCall, variables2, name, name, returnCallEnd);
          Printf(listenerBody, "void EmRunOnMainThread::%s (void* arg) {\n    em_queued_call* q = (em_queued_call*)arg;\n    %sWrapper* self = (%sWrapper*) q->args[0].vp;\n%s\n%s    q->operationDone = 1;\n    emscripten_futex_wake(&q->operationDone, INT_MAX);\n}\n", name, className, className, variables3, returnBody);
        }
      }

      Printf(listenerHeader, "};\n");
      Printf(listenerCall, "};\n");
      Printf(f_cxx_wrapper, "%s\n\n%s\n\n%s\n", listenerHeader, listenerCall, listenerBody);
    }

    String *super = NewString("");
    if (bases) {
      Node *base = First(bases).item;
      bool isVirtualBase = inheritsVirtually(n, base);
      Printf(super, isVirtualBase ? ", crossbind::VirtualBase<%s>" : ", emscripten::base<%s>", Getattr(base, "name"));
      if (isVirtualBase) usesPointerRuntime = true;
    }

    Printf(f_cxx_functions, "    if (crossbind::claimType(typeid(std::vector<std::shared_ptr<%s>>), \"Vector%s\")) emscripten::register_vector<std::shared_ptr<%s>>(\"Vector%s\");\n", nsname, name, nsname, name);
    Printf(exports, ", \"Vector%s\"", name);
    // embind registers `delete` as every class's destructor, which a protected or private destructor refuses; such a
    // class manages its own lifetime (GEOS's GeometryFactory), so JS delete() leaves the object alone.
    if (Getattr(n, "allocate:has_destructor") && !Getattr(n, "allocate:default_destructor")) {
      Printf(f_cxx_wrapper, "namespace emscripten { namespace internal { template<> inline void raw_destructor<%s>(%s *) {} } }\n\n", nsname, nsname);
    }
    // Member signatures can spell types relative to the class namespace (types SWIG never saw), so the block reopens it.
    List *namespaces = enclosingNamespaces(n);
    for (Iterator ns = First(namespaces); ns.item; ns = Next(ns)) Printf(f_cxx_wrapper, "namespace %s { ", ns.item);
    if (Len(namespaces) != 0) Printf(f_cxx_wrapper, "\n");
    // The claim spells the type through typeid: crossbind finds the class_ opener by its `>("Name")`.
    Printf(f_cxx_wrapper, "EMSCRIPTEN_BINDINGS(%s) {\n  if (crossbind::claimType(typeid(%s), \"%s\")) emscripten::class_<%s%s>(\"%s\")\n", name, nsname, name, nsname, super, name);
    Printf(exports, ", \"%s\"", name);
    if (Getattr(n, "feature:shared_ptr")) Printf(f_cxx_wrapper, "    .smart_ptr<std::shared_ptr<%s>>(\"%s\")\n", nsname, name);
    if (isListener) Printf(f_cxx_wrapper, "    .allow_subclass<%sWrapper, std::shared_ptr<%sWrapper>>(\"%sWrapper\", \"%sWrapperSharedPtr\")\n", name, name, name, name);
    Language::classHandler(n);
    Printf(f_cxx_wrapper, "  ;\n}\n");
    for (Iterator ns = First(namespaces); ns.item; ns = Next(ns)) Printf(f_cxx_wrapper, "}");
    Printf(f_cxx_wrapper, Len(namespaces) != 0 ? "\n\n" : "\n");
    Printf(f_cxx_wrapper, "%s", deferredBlocks);
    Clear(deferredBlocks);
    Delete(namespaces);
  }

  return SWIG_OK;
}

int EMBIND::constructorHandler(Node *n) {
  Language::constructorHandler(n);
  return SWIG_OK;
}

int EMBIND::destructorHandler(Node *n) {
  Language::destructorHandler(n);
  return SWIG_OK;
}

int EMBIND::memberfunctionHandler(Node *n) {
  return Language::memberfunctionHandler(n);
}

int EMBIND::membervariableHandler(Node *n) {
  return Language::membervariableHandler(n);
}

static bool isStandardStream(const SwigType *t) {
  SwigType *bare = bareType(t);
  String *prefix = SwigType_templateprefix(bare);
  String *last = Swig_scopename_last(prefix);
  bool result = Strncmp(bare, "std::", 5) == 0 && Len(last) >= 6 && Strcmp(Char(last) + Len(last) - 6, "stream") == 0;
  Delete(last);
  Delete(prefix);
  Delete(bare);
  return result;
}

// A move-only value (a container of std::unique_ptr, or a std::unique_ptr with its own deleter) passed by value or as an
// rvalue: embind can only copy what it hands over, and JS cannot build such a value anyway.
static bool isMoveOnlyByValue(const SwigType *t) {
  return !SwigType_ispointer(t) && !SwigType_isreference(t) && returnsMoveOnly(t);
}

// JS cannot call these, and their bindings do not compile: deleted members, friends declared only inside their class
// (ordinary lookup cannot find them), move constructors, standard streams, and move-only values passed by value.
static const char *unbindableReason(Node *n) {
  if (GetFlag(n, "deleted")) return "is deleted";
  String *storage = Getattr(n, "storage");
  if (storage && Strstr(storage, "friend")) return "is declared as a friend";
  ParmList *parms = Getattr(n, "parms");
  if (Equal(nodeType(n), "constructor") && parms && !nextSibling(parms) && SwigType_isrvalue_reference(Getattr(parms, "type"))) {
    Node *owner = parentNode(n);
    if (owner && Equal(nodeType(owner), "extend")) owner = parentNode(owner);
    SwigType *bare = bareType(Getattr(parms, "type"));
    bool isMove = owner && Equal(bare, Getattr(owner, "name"));
    Delete(bare);
    if (isMove) return "is a move constructor";
  }
  if (isStandardStream(Getattr(n, "type"))) return "returns a standard stream";
  for (Parm *p = parms; p; p = nextSibling(p)) {
    if (isStandardStream(Getattr(p, "type"))) return "takes a standard stream";
    if (isMoveOnlyByValue(Getattr(p, "type"))) return "takes a move-only value by value";
  }
  return 0;
}

int EMBIND::functionWrapper(Node *n) {
  if (takesVariadicArguments(Getattr(n, "parms"))) {
    Swig_warning(WARN_LANG_VARARGS, Getfile(n), Getline(n), "Variable length arguments are not supported by embind, %s skipped.\n", Getattr(n, "name"));
    return SWIG_OK;
  }
  if (const char *reason = unbindableReason(n)) {
    Swig_warning(WARN_LANG_IDENTIFIER, Getfile(n), Getline(n), "%s %s, so embind cannot bind it; skipped.\n", Getattr(n, "name"), reason);
    return SWIG_OK;
  }
  String   *bname   = Getattr(n, "sym:name");
  SwigType *btype   = Getattr(n, "type");
  ParmList *bparms  = Getattr(n, "parms");
  String   *bparmstr= ParmList_str_defaultargs(bparms); // to string
  String   *bfunc   = SwigType_str(btype, NewStringf("%s(%s)", bname, bparmstr));

  String *wrap = Getattr(n, "wrap:code");
  String *actioncode = emit_action(n);
  // Printf(f_cxx_wrapper, "\n\na - %s\n", wrap);

  auto actioncodeString = std::string(Char(actioncode));
  int i = findStartOfParenthesis(actioncodeString);
  if (i > 0) {
    actioncodeString = actioncodeString.substr(0, i);
  }
  i = findEndOfParenthesisOrBlank(actioncodeString);
  if (i > 0) {
    actioncodeString = actioncodeString.substr(i + 1);
  }
  // A function returning a reference is called through its address: `result = (T *) &T::make(...)`.
  if (!actioncodeString.empty() && actioncodeString[0] == '&') actioncodeString.erase(0, 1);

  ParmList *parms = Getattr(n, "parms");
  String *name = Getattr(n, "name");
  String *name2 = Getattr(n, "memberfunctionHandler:sym:name");
  String *staticName = Getattr(n, "staticmemberfunctionHandler:name");
  String *variableName = Getattr(n, "membervariableHandler:sym:name");
  String *type = Getattr(n, "nodeType");
  String *view = Getattr(n, "view");



  /* if (Strcmp(type, "constructor") != 0 && Strcmp(Getitem(returnTypeSplit, 0), "p") == 0) {
    return SWIG_OK;
  } */

  std::string nameStr = std::string(Char(name));

  if (nameStr.length() > 9 && nameStr.substr(0, 9) == "operator ") {
    return SWIG_OK;
  }


  Node *parent = parentNode(n);
  String *className = Getattr(parent, "name");
  String *parentNodeType = Getattr(parent, "nodeType");
  if (Strcmp(parentNodeType, "extend") == 0) {
    parent = parentNode(parent);
    className = Getattr(parent, "name");
  }

  if (Len(className) != 0 && actioncodeString.substr(0, 2) == "->") {
    actioncodeString = std::string(Char(className)) + "::" + actioncodeString.substr(2);
  }

  String *funcName = NewString(actioncodeString.c_str());

  // Printf(f_cxx_wrapper, "\n\n%s\n", funcName);

  // Printf(f_cxx_wrapper, "\n\n\n%s - %s\n", className, parent);
  // Printf(f_cxx_wrapper, "%s\n", n);
  bool isListener = Len(className) > 8 && std::string(Char(className)).substr(Len(className) - 8) == "Listener";
  bool isUsingSameName = false;

  int order = 0;
  bool order_break = false;

  for (Node *c = firstChild(parent); c; c = nextSibling(c)) {
    String *childName = Getattr(c, "name");
    
    if (!childName) continue;

    if (c == n) {
      order_break = true;
      continue;
    }
    std::string childNameStr = std::string(Char(childName));

    std::string realNameStr = "";
    if (Len(name) != 0 && Len(name2) != 0) {
      realNameStr = nameStr;
    } else if (Len(staticName) != 0) {
      realNameStr = std::string(Char(staticName));
    } else if (Equal(type, "cdecl") && Equal(nodeType(c), "cdecl") && Getattr(c, "decl") && SwigType_isfunction(Getattr(c, "decl"))) {
      // A namespaced free function is named with its scope, its siblings may not be.
      realNameStr = Char(Swig_scopename_last(name));
      childNameStr = Char(Swig_scopename_last(childName));
    }

    if (realNameStr == "") continue;

    if (childNameStr == realNameStr) {
      isUsingSameName = true;
      if (!order_break) order += 1;
    }
  }
  
  String *smartPtrParams = NewString("");
  String *constructorParams = NewString("");
  {
    ParmList *pl = Getattr(n, "parms");
    int argnum = 0;
    for (Parm *p = pl; p; p = nextSibling(p), argnum++) {
      String *tempPType = Getattr(p, "type");
      std::string tempPTypeStr = std::string(Char(tempPType));

      /* if (Strcmp(type, "constructor") == 0 || Len(staticName) != 0 || argnum > 0) {
        if (tempPTypeStr.length() > 2 && tempPTypeStr.substr(0, 2) == "p.") {
          return SWIG_OK;
        }
      } */

      SwigType *spelledType = withoutMemberAliases(tempPType, className);
      String *pTypeSplit = Split(spelledType, '.', -1);
      String *pType = Getitem(pTypeSplit, Len(pTypeSplit) - 1);
      Replace(pType, "(", "", DOH_REPLACE_ANY);
      Replace(pType, ")", "", DOH_REPLACE_ANY);
      if (spellsPointer(spelledType)) {
        pType = SwigType_str(spelledType, 0);
      }
      // A class-scoped `typedef enum {...} Type;` cannot be spelled with the enum keyword (GEOS PrecisionModel).
      Replace(pType, "enum ", "", DOH_REPLACE_ANY);

      if (argnum == 0) Printf(constructorParams, "%s", pType);
      else Printf(constructorParams, ", %s", pType);

      Printf(smartPtrParams, ", %s", pType);
    }
  }

  bool isConstructor = Strcmp(type, "constructor") == 0;
  bool needsAdapter = !isConstructor && (returnsMoveOnly(Getattr(n, "type")) || returnForm(n) != PLAIN_ARGUMENT || returnsReferenceAsPointer(n) || returnsUniquePtrReference(n) || returnsUncopyableValue(n) || returnsUnknownValue(n) || returnsVectorOfUnknown(n));
  bool hasRawPointer = !isConstructor && !needsAdapter && (isRawPointer(Getattr(n, "type")) || mayHidePointer(n, Getattr(n, "type")));
  for (Parm *p = parms; p; p = nextSibling(p)) {
    if (GetFlag(p, "self")) continue;
    if (argumentForm(n, Getattr(p, "type"), 0) != PLAIN_ARGUMENT) {
      needsAdapter = true;
    } else if (isRawPointer(Getattr(p, "type")) || mayHidePointer(n, Getattr(p, "type"))) {
      hasRawPointer = true;
    }
    // A reference spelled as a make_shared or constructor<> argument would be copied, which abstract classes refuse.
    if (isConstructor && (SwigType_isreference(Getattr(p, "type")) || SwigType_isrvalue_reference(Getattr(p, "type")))) needsAdapter = true;
  }
  // crossbind::JsPointer resolves to a raw class pointer when the pointee type is complete.
  String *pointerPolicy = NewString(hasRawPointer || needsAdapter ? ", emscripten::allow_raw_pointers()" : "");

  if (isConstructor) {
    if (!claimOverload(n, "constructor", className, name, parms)) return SWIG_OK;
    bool isPolymorphic = Getattr(parent, "feature:polymorphic_shared_ptr") != 0;
    if (needsAdapter) {
      String *callee = NewStringf(isPolymorphic ? "std::make_shared<%s>" : "new %s", className);
      if (isPolymorphic) {
        Printf(f_cxx_wrapper, "    .smart_ptr_constructor(\"%s\", %s%s)\n", name, bindingAdapter(n, parms, callee, className), pointerPolicy);
      } else {
        Printf(f_cxx_wrapper, "    .constructor(%s)\n", bindingAdapter(n, parms, callee, className));
      }
    } else if (isPolymorphic) {
      // SWIG assumes a constructor it parsed is usable even where a base or member from a header it never parsed deletes
      // it or keeps the class abstract; the template instantiates make_shared only for constructible classes.
      static bool isFactoryPrinted = false;
      if (!isFactoryPrinted) {
        Printf(f_cxx_header, "\n#include <memory>\n#include <stdexcept>\n#include <type_traits>\n#include <utility>\n\nnamespace crossbind {\ntemplate<typename T, typename... A> std::shared_ptr<T> makeShared(A... args) {\n  if constexpr (std::is_constructible_v<T, A...>) return std::make_shared<T>(std::forward<A>(args)...);\n  else throw std::invalid_argument(\"crossbind: this class cannot be constructed from these arguments\");\n}\n}\n");
        isFactoryPrinted = true;
      }
      Printf(f_cxx_wrapper, "    .smart_ptr_constructor(\"%s\", &crossbind::makeShared<%s%s>%s)\n", name, className, smartPtrParams, pointerPolicy);
    } else {
      // class_::constructor already allows raw pointers; a policy argument would bind to its Callable overload.
      Printf(f_cxx_wrapper, "    .constructor<%s>()\n", constructorParams);
    }
  } else if (Len(className) != 0) {
    String *params = NewString("");
    String *variables = NewString("");
    ParmList *pl = Getattr(n, "parms");
    int argnum = 0;
    for (Parm *p = pl; p; p = nextSibling(p), argnum++) {
      String *pName = Getattr(p, "name");

      if (Len(pName) == 0) {
        pName = Getattr(p, "lname");
      }

      if (Strcmp(pName, "self") == 0) {
        --argnum;
        continue;
      }

      SwigType *spelledType = withoutMemberAliases(Getattr(p, "type"), className);
      String *pTypeSplit = Split(spelledType, '.', -1);
      String *pType = Getitem(pTypeSplit, Len(pTypeSplit) - 1);
      Replace(pType, "(", "", DOH_REPLACE_ANY);
      Replace(pType, ")", "", DOH_REPLACE_ANY);
      String *pTypeAll = NewString("");
      if (Len(pTypeSplit) > 1 && Strcmp(Getitem(pTypeSplit, Len(pTypeSplit) - 2), "q(const)") == 0) {
        String *temp = NewString("");
        Printf(temp, "const %s&", pType);
        pType = temp;
      }
      if (spellsPointer(spelledType)) {
        pType = SwigType_str(spelledType, 0);
      }
      Printf(pTypeAll, "%s %s", pType, pName);

      if (argnum == 0) {
        Printf(variables, "%s", pName);
      } else {
        Printf(variables, ", %s", pName);
      }
      Printf(params, ", %s", pTypeAll);
    }

    if (Len(variableName) != 0) {

    } else if (Len(staticName) != 0 && Strcmp(view, "destructorHandler") != 0) {
      bool isJSPI = strstr(Char(staticName), "_JSPI") != nullptr;
      // A JS class is a function, and its length, name and prototype properties cannot be replaced.
      if (Equal(staticName, "length") || Equal(staticName, "name") || Equal(staticName, "prototype")) {
        Swig_warning(WARN_LANG_IDENTIFIER, Getfile(n), Getline(n), "Static method %s cannot become a property of a JavaScript class, skipped.\n", staticName);
        return SWIG_OK;
      }
      if (!claimOverload(n, "static", className, staticName, parms)) return SWIG_OK;
      // Overloads go through a lambda, so the compiler applies default arguments and chooses among template overloads.
      if (needsAdapter || isUsingSameName) {
        Printf(f_cxx_wrapper, "    .class_function(\"%s\", %s%s%s)\n", staticName, bindingAdapter(n, parms, funcName, className), isJSPI && !isUsingSameName ? ", emscripten::async()" : "", pointerPolicy);
      } else if (isJSPI) {
        Printf(f_cxx_wrapper, "    .class_function(\"%s\", &%s, emscripten::async()%s)\n", staticName, funcName, pointerPolicy);
      } else {
        Printf(f_cxx_wrapper, "    .class_function(\"%s\", &%s%s)\n", staticName, funcName, pointerPolicy);
      }
    } else if (Len(name) != 0 && Strcmp(view, "destructorHandler") != 0) {
      bool isJSPI = strstr(Char(name), "_JSPI") != nullptr;
      if (Len(name2) != 0) {
        if (!claimOverload(n, "method", className, name, parms)) return SWIG_OK;
        if (isListener) {
          if (Getattr(n, "abstract")) {
            Printf(f_cxx_wrapper, "    .function(\"%s\", &%s::%s, emscripten::pure_virtual())\n", name, className, name);
          } else {
            Printf(f_cxx_wrapper, "    .function(\"%s\", emscripten::optional_override([](%s& self%s) {\n      return self.%s(%s);\n    }))\n", name, className, params, name, variables);
          }
        } else if (needsAdapter || isUsingSameName) {
          String *callee = NewStringf("self->%s", name);
          Printf(f_cxx_wrapper, "    .function(\"%s\", %s%s, emscripten::allow_raw_pointers())\n", name, bindingAdapter(n, parms, callee, className), isJSPI && !isUsingSameName ? ", emscripten::async()" : "");
        } else if (isJSPI) {
          Printf(f_cxx_wrapper, "    .function(\"%s\", &%s, emscripten::async()%s)\n", name, funcName, pointerPolicy);
        } else {
          Printf(f_cxx_wrapper, "    .function(\"%s\", &%s%s)\n", name, funcName, pointerPolicy);
        }
      } else {
        // A namespaced free function keeps its C++ qualification; its JS export name cannot carry `::`.
        String *jsName = Swig_scopename_last(name);
        if (!claimOverload(n, "function", "", jsName, parms)) return SWIG_OK;
        if (needsAdapter || isUsingSameName) {
          String *registration = NewStringf("    if (crossbind::claimFunction(\"%s\", %d)) emscripten::function(\"%s\", %s%s%s);\n", jsName, bindingArity(parms), jsName, bindingAdapter(n, parms, name, className), isJSPI && !isUsingSameName ? ", emscripten::async()" : "", pointerPolicy);
          List *namespaces = enclosingNamespaces(n);
          if (Len(namespaces) == 0) {
            Printf(f_cxx_functions, "%s", registration);
          } else {
            // The adapter spells parameter types as the header does, relative to the function's namespace, which its block reopens.
            static int namespacedFunctionBlocks = 0;
            for (Iterator ns = First(namespaces); ns.item; ns = Next(ns)) Printf(f_cxx_wrapper, "namespace %s { ", ns.item);
            Printf(f_cxx_wrapper, "\nEMSCRIPTEN_BINDINGS(Function_%s_%d) {\n%s}\n", jsName, ++namespacedFunctionBlocks, registration);
            for (Iterator ns = First(namespaces); ns.item; ns = Next(ns)) Printf(f_cxx_wrapper, "}");
            Printf(f_cxx_wrapper, "\n\n");
          }
          Delete(namespaces);
          Delete(registration);
        } else if (isJSPI) {
          Printf(f_cxx_functions, "    if (crossbind::claimFunction(\"%s\", %d)) emscripten::function(\"%s\", &%s, emscripten::async()%s);\n", jsName, bindingArity(parms), jsName, name, pointerPolicy);
        } else {
          Printf(f_cxx_functions, "    if (crossbind::claimFunction(\"%s\", %d)) emscripten::function(\"%s\", &%s%s);\n", jsName, bindingArity(parms), jsName, name, pointerPolicy);
        }
        String *exported = NewStringf("\"%s\"", jsName);
        if (!Strstr(exports, exported)) Printf(exports, ", %s", exported);
        Delete(exported);
      }
    }
  }

  return SWIG_OK;
}

int EMBIND::constantWrapper(Node *n) {
  return SWIG_OK;
}

int EMBIND::variableWrapper(Node *n) {
  return SWIG_OK;
}

int EMBIND::typedefHandler(Node *n) {
  return Language::typedefHandler(n);
}

int EMBIND::enumDeclaration(Node *n) {
  if (!ImportMode) {
      if (getCurrentClass() && (cplus_mode != PUBLIC)) return SWIG_NOWRAP;

      String *symname = Getattr(n, "sym:name");
      String *name = Getattr(n, "name");
      // embind registers enums by type; the values of a nameless enum reach JS as the ints its functions take.
      if (!name || !symname || Len(name) == 0 || Len(symname) == 0) return SWIG_NOWRAP;

      // A class-scoped enum is reached while its class chain is still open: emit it after the class block.
      String *out = getCurrentClass() ? deferredBlocks : f_cxx_wrapper;
      // Classes can scope enums of the same name (PROJ's WKTFormatter::Convention and PROJStringFormatter::Convention):
      // a later one is registered under its class name.
      String *jsName = Copy(symname);
      String *key = NewStringf("enum %s", jsName);
      if (Getattr(boundOverloads, key) && getCurrentClass()) {
        Delete(jsName);
        Delete(key);
        jsName = NewStringf("%s_%s", Getattr(getCurrentClass(), "sym:name"), symname);
        key = NewStringf("enum %s", jsName);
      }
      Setattr(boundOverloads, key, "1");
      Delete(key);
      Printf(out, "EMSCRIPTEN_BINDINGS(%s) {\n  if (crossbind::claimType(typeid(%s), \"%s\")) emscripten::enum_<%s>(\"%s\")\n", jsName, name, jsName, name, jsName);
      Printf(exports, ", \"%s\"", jsName);
      Delete(jsName);

      for (Node *c = firstChild(n); c; c = nextSibling(c)) {
        String *cName = Getattr(c, "name");
        String *cValue = Getattr(c, "value");
        Printf(out, "    .value(\"%s\", %s)\n", cName, cValue);
      }

      Printf(out, "    ;\n}\n\n");
  }

  return SWIG_OK;
}

extern "C" Language *swig_embind(void) {
  return new EMBIND();
}
