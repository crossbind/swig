
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace crossbind {
template<typename T, typename = void> struct IsComplete : std::false_type {};
template<typename T> struct IsComplete<T, std::void_t<decltype(sizeof(T))>> : std::true_type {};
template<typename T> struct IsBasicString : std::false_type {};
template<typename C, typename Traits, typename Allocator> struct IsBasicString<std::basic_string<C, Traits, Allocator>> : std::true_type {};
template<typename Q> constexpr bool isRawPointee = IsComplete<Q>::value && (std::is_class_v<Q> || std::is_union_v<Q>) && !IsBasicString<std::remove_cv_t<Q>>::value;
template<typename T> inline const char pointeeTag = 0;
struct NativePointer {
  std::uintptr_t address;
  const char *pointee;
  bool readOnly;
  std::shared_ptr<void> storage;
  size_t capacity = 0;
  const char *element = nullptr;
  bool elementReadOnly = false;
  std::vector<std::shared_ptr<NativePointer>> retained;
};
using PointerHandle = std::shared_ptr<NativePointer>;
template<typename Q> using JsPointer = std::conditional_t<isRawPointee<Q>, Q *, PointerHandle>;
template<typename T> void recordElement(NativePointer &p) {
  if constexpr (std::is_pointer_v<T>) {
    p.element = &pointeeTag<std::remove_cv_t<std::remove_pointer_t<T>>>;
    p.elementReadOnly = std::is_const_v<std::remove_pointer_t<T>>;
  }
}
template<typename T> constexpr bool acceptsUntypedMemory = std::disjunction_v<std::negation<IsComplete<T>>, std::is_trivially_copyable<T>>;
template<typename Q> Q *fromJs(Q *p) { return p; }
template<typename Q> Q *fromJs(const PointerHandle &p) {
  if (!p) return nullptr;
  if (!std::is_const_v<Q> && p->readOnly) throw std::invalid_argument("crossbind: a read-only pointer cannot be passed as a mutable pointer");
  using T = std::remove_cv_t<Q>;
  const char *expected = &pointeeTag<T>;
  bool slot = std::is_pointer_v<T> && p->pointee == &pointeeTag<void *>;
  bool untyped = p->pointee == &pointeeTag<void> && acceptsUntypedMemory<T>;
  if (p->pointee != expected && !untyped && expected != &pointeeTag<void> && !slot) throw std::invalid_argument("crossbind: pointer type mismatch");
  recordElement<T>(*p);
  return reinterpret_cast<Q *>(p->address);
}
template<typename Q> PointerHandle toHandle(Q *p) {
  if (!p) return nullptr;
  PointerHandle handle = std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(p), &pointeeTag<std::remove_cv_t<Q>>, std::is_const_v<Q>, nullptr});
  recordElement<std::remove_cv_t<Q>>(*handle);
  return handle;
}
template<typename Q> JsPointer<Q> toJs(Q *p) {
  if constexpr (isRawPointee<Q>) return p;
  else return toHandle(p);
}
struct CStringArg {
  bool isText = false;
  std::string text;
  PointerHandle handle;
  const char *pointer = nullptr;
  operator const char *() const { return isText ? text.c_str() : pointer; }
};
template<typename Q> CStringArg fromJsCString(const emscripten::val &value) {
  CStringArg arg;
  if (value.isNull() || value.isUndefined()) return arg;
  if (value.isString()) {
    arg.isText = true;
    arg.text = value.as<std::string>();
  } else if (value.instanceof(emscripten::val::module_property("NativePointer"))) {
    arg.handle = value.as<PointerHandle>();
    arg.pointer = fromJs<const char>(arg.handle);
  } else {
    throw std::invalid_argument("crossbind: a const char* parameter takes a string, a pointer handle or null");
  }
  return arg;
}
#ifdef __EMSCRIPTEN__
template<typename Q> using JsCString = emscripten::val;
inline emscripten::val toJsCString(const char *text) { return text ? emscripten::val(std::string(text)) : emscripten::val::null(); }
#else
template<typename Q> using JsCString = facebook::jsi::Value;
template<typename Q> CStringArg fromJsCString(const facebook::jsi::Value &value) {
  facebook::jsi::Runtime &runtime = *emscripten::jsRuntime;
  if (value.isNull() || value.isUndefined()) return CStringArg();
  if (!value.isString()) return fromJsCString<Q>(emscripten::val(facebook::jsi::Value(runtime, value)));
  CStringArg arg;
  arg.isText = true;
  arg.text = value.getString(runtime).utf8(runtime);
  return arg;
}
inline facebook::jsi::Value toJsCString(const char *text) {
  if (!text) return facebook::jsi::Value::null();
  return facebook::jsi::String::createFromUtf8(*emscripten::jsRuntime, reinterpret_cast<const uint8_t *>(text), std::strlen(text));
}
#endif
template<typename Q> using JsStructPointer = std::conditional_t<isRawPointee<Q>, emscripten::val, PointerHandle>;
template<typename Q> Q *fromJsStruct(const PointerHandle &p) { return fromJs<Q>(p); }
template<typename Q> Q *fromJsStruct(const emscripten::val &value) {
  if (value.isNull() || value.isUndefined()) return nullptr;
  if (value.instanceof(emscripten::val::module_property("NativePointer"))) return fromJs<Q>(value.as<PointerHandle>());
  return value.as<Q *>(emscripten::allow_raw_pointers());
}
template<typename T> std::shared_ptr<T> fieldView(T *pointer) { return std::shared_ptr<T>(pointer, [](T *) {}); }
template<typename P> P fieldFromJs(const emscripten::val &value) {
  using Q = std::remove_pointer_t<P>;
  if constexpr (isRawPointee<std::remove_cv_t<Q>>) return fromJsStruct<Q>(value);
  else return value.isNull() || value.isUndefined() ? nullptr : fromJs<Q>(value.as<PointerHandle>());
}
template<auto M, bool Instance, typename Builder> void bindPointerField(const Builder &cls, const char *name) {
  using C = typename MemberOf<decltype(M)>::Class;
  using T = typename MemberOf<decltype(M)>::Type;
  auto read = +[](const C &s) {
    if constexpr (Instance) return fieldView(s.*M);
    else return toHandle(s.*M);
  };
  if constexpr (std::is_const_v<T>) cls.property(name, read);
  else cls.property(name, read, +[](C &s, emscripten::val v) { s.*M = fieldFromJs<std::remove_cv_t<T>>(v); });
}
template<typename T> constexpr bool isFunctionPointer = std::is_pointer_v<T> && std::is_function_v<std::remove_pointer_t<T>>;
#ifdef __EMSCRIPTEN__
template<typename F> using JsCallback = emscripten::val;
#else
template<typename F> using JsCallback = facebook::jsi::Value;
#endif
inline constexpr size_t callbackSlotCount = 64;
template<typename A> auto callbackArgument(std::remove_reference_t<A> &value) {
  using U = std::remove_cv_t<std::remove_reference_t<A>>;
  if constexpr (std::is_same_v<U, const char *>) return toJsCString(value);
  else if constexpr (std::is_pointer_v<U>) return toHandle(value);
  else if constexpr (std::is_enum_v<U>) return static_cast<std::underlying_type_t<U>>(value);
  else if constexpr (std::is_class_v<U> || std::is_union_v<U>) return toHandle(&value);
  else return U(value);
}
#ifndef __EMSCRIPTEN__
struct RuntimeCallbacks {
  std::array<std::optional<facebook::jsi::Function>, callbackSlotCount> functions;
};
struct RuntimeCallbacksCache {
  facebook::jsi::Runtime *runtime = nullptr;
  std::weak_ptr<RuntimeCallbacks> callbacks;
};
inline RuntimeCallbacksCache &runtimeCallbacksCache() {
  thread_local RuntimeCallbacksCache cache;
  return cache;
}
inline std::shared_ptr<RuntimeCallbacks> cachedRuntimeCallbacks() {
  RuntimeCallbacksCache &cache = runtimeCallbacksCache();
  return cache.runtime == emscripten::jsRuntime ? cache.callbacks.lock() : nullptr;
}
inline RuntimeCallbacks &runtimeCallbacks(facebook::jsi::Runtime &runtime) {
  static constexpr facebook::jsi::UUID key{0x63627263, 0x616c, 0x6c62, 0x8163, 0x6b73636272ull};
  std::shared_ptr<RuntimeCallbacks> callbacks = cachedRuntimeCallbacks();
  if (!callbacks) {
    callbacks = std::static_pointer_cast<RuntimeCallbacks>(runtime.getRuntimeData(key));
    if (!callbacks) {
      callbacks = std::make_shared<RuntimeCallbacks>();
      runtime.setRuntimeData(key, callbacks);
    }
    runtimeCallbacksCache() = {&runtime, callbacks};
  }
  return *callbacks;
}
template<typename T, bool = std::is_enum_v<T>> struct WireOf { using type = T; };
template<typename T> struct WireOf<T, true> { using type = std::underlying_type_t<T>; };
template<typename T> constexpr bool isPlainWire = std::is_same_v<T, bool> || std::is_same_v<T, char> || std::is_same_v<T, signed char> || std::is_same_v<T, unsigned char> || std::is_same_v<T, short> || std::is_same_v<T, unsigned short> || std::is_same_v<T, int> || std::is_same_v<T, unsigned int> || std::is_same_v<T, float> || std::is_same_v<T, double>;
template<typename T> constexpr bool isDirectCallbackValue = isPlainWire<T> || std::is_same_v<T, facebook::jsi::Value>;
template<typename T> facebook::jsi::Value callbackValue(facebook::jsi::Runtime &runtime, const T &value) {
  if constexpr (std::is_same_v<T, facebook::jsi::Value>) return facebook::jsi::Value(runtime, value);
  else return emscripten::internal::BindingType<T>::toWireType2(runtime, value);
}
template<typename W> bool fitsPlainWire(const facebook::jsi::Value &result) {
  if constexpr (std::is_same_v<W, bool>) return result.isBool();
  else if constexpr (std::is_floating_point_v<W>) return result.isNumber();
  else return result.isNumber() && result.getNumber() >= std::numeric_limits<W>::min() && result.getNumber() <= std::numeric_limits<W>::max();
}
template<typename R, typename... A> R invokeCallback(size_t slot, A... args) {
  std::shared_ptr<RuntimeCallbacks> callbacks = cachedRuntimeCallbacks();
  if (!callbacks || !callbacks->functions[slot]) {
    std::fprintf(stderr, "crossbind: C called a callback that JS released, or called it from another thread than the one that passed it\n");
    return R();
  }
  facebook::jsi::Runtime &runtime = *emscripten::jsRuntime;
  const facebook::jsi::Function &function = *callbacks->functions[slot];
  constexpr bool isDirect = (isDirectCallbackValue<decltype(callbackArgument<A>(std::declval<std::remove_reference_t<A> &>()))> && ...) && (std::is_void_v<R> || std::is_arithmetic_v<R> || std::is_enum_v<R>);
  if constexpr (isDirect) {
    facebook::jsi::Value result = function.call(runtime, callbackValue(runtime, callbackArgument<A>(args))...);
    if constexpr (std::is_void_v<R>) return;
    else {
      using W = typename WireOf<R>::type;
      if constexpr (isPlainWire<W>) {
        if (fitsPlainWire<W>(result)) return static_cast<R>(emscripten::internal::BindingType<W>::fromWireType2(runtime, result));
      }
      return static_cast<R>(emscripten::val(std::move(result)).as<W>());
    }
  } else {
    emscripten::val result = emscripten::val(facebook::jsi::Value(runtime, function))(callbackArgument<A>(args)...);
    if constexpr (std::is_void_v<R>) return;
    else if constexpr (std::is_pointer_v<R>) return result.isNull() || result.isUndefined() ? nullptr : fromJs<std::remove_pointer_t<R>>(result.as<PointerHandle>());
    else if constexpr (std::is_enum_v<R>) return static_cast<R>(result.as<std::underlying_type_t<R>>());
    else return result.as<R>();
  }
}
#else
inline std::array<std::optional<emscripten::val>, callbackSlotCount> &callbackSlots() {
  thread_local std::array<std::optional<emscripten::val>, callbackSlotCount> slots;
  return slots;
}
template<typename R, typename... A> R invokeCallback(size_t slot, A... args) {
  std::optional<emscripten::val> &function = callbackSlots()[slot];
  if (!function) {
    std::fprintf(stderr, "crossbind: C called a callback that JS released, or called it from another thread than the one that passed it\n");
    return R();
  }
  emscripten::val result = (*function)(callbackArgument<A>(args)...);
  if constexpr (std::is_void_v<R>) return;
  else if constexpr (std::is_pointer_v<R>) return result.isNull() || result.isUndefined() ? nullptr : fromJs<std::remove_pointer_t<R>>(result.as<PointerHandle>());
  else if constexpr (std::is_enum_v<R>) return static_cast<R>(result.as<std::underlying_type_t<R>>());
  else return result.as<R>();
}
#endif
template<typename F> struct Callback { static constexpr bool isSupported = false; };
template<typename R, typename... A> struct Callback<R (*)(A...)> {
  static constexpr bool isSupported = true;
  template<size_t I> static R call(A... args) { return invokeCallback<R, A...>(I, std::forward<A>(args)...); }
};
template<typename F, size_t... I> constexpr std::array<F, sizeof...(I)> callbackTable(std::index_sequence<I...>) { return {{&Callback<F>::template call<I>...}}; }
template<typename F> inline constexpr std::array<F, callbackSlotCount> trampolines = callbackTable<F>(std::make_index_sequence<callbackSlotCount>());
#ifndef __EMSCRIPTEN__
inline size_t claimCallbackSlot(facebook::jsi::Runtime &runtime, const facebook::jsi::Object &function) {
  RuntimeCallbacks &callbacks = runtimeCallbacks(runtime);
  for (size_t i = 0; i < callbackSlotCount; ++i) {
    if (callbacks.functions[i] && facebook::jsi::Object::strictEquals(runtime, *callbacks.functions[i], function)) return i;
  }
  for (size_t i = 0; i < callbackSlotCount; ++i) {
    if (!callbacks.functions[i]) {
      callbacks.functions[i] = function.getFunction(runtime);
      return i;
    }
  }
  throw std::length_error("crossbind: every callback slot holds a function; releaseCallback frees the ones C no longer calls");
}
template<typename F> F fromJsCallback(const facebook::jsi::Value &value) {
  facebook::jsi::Runtime &runtime = *emscripten::jsRuntime;
  if (value.isNull() || value.isUndefined()) return nullptr;
  if (!value.isObject() || !value.getObject(runtime).isFunction(runtime)) return fromJs<std::remove_pointer_t<F>>(emscripten::val(facebook::jsi::Value(runtime, value)).as<PointerHandle>());
  if constexpr (Callback<F>::isSupported) return trampolines<F>[claimCallbackSlot(runtime, value.getObject(runtime))];
  else throw std::invalid_argument("crossbind: a JS function cannot stand in for a variadic C callback");
}
inline bool releaseCallback(const facebook::jsi::Value &function) {
  facebook::jsi::Runtime &runtime = *emscripten::jsRuntime;
  if (!function.isObject()) return false;
  facebook::jsi::Object object = function.getObject(runtime);
  for (std::optional<facebook::jsi::Function> &slot : runtimeCallbacks(runtime).functions) {
    if (slot && facebook::jsi::Object::strictEquals(runtime, *slot, object)) {
      slot.reset();
      return true;
    }
  }
  return false;
}
#else
inline size_t claimCallbackSlot(const emscripten::val &function) {
  std::array<std::optional<emscripten::val>, callbackSlotCount> &slots = callbackSlots();
  for (size_t i = 0; i < callbackSlotCount; ++i) {
    if (slots[i] && slots[i]->strictlyEquals(function)) return i;
  }
  for (size_t i = 0; i < callbackSlotCount; ++i) {
    if (!slots[i]) {
      slots[i] = function;
      return i;
    }
  }
  throw std::length_error("crossbind: every callback slot holds a function; releaseCallback frees the ones C no longer calls");
}
template<typename F> F fromJsCallback(const emscripten::val &value) {
  if (value.isNull() || value.isUndefined()) return nullptr;
  if (value.typeOf().as<std::string>() != "function") return fromJs<std::remove_pointer_t<F>>(value.as<PointerHandle>());
  if constexpr (Callback<F>::isSupported) return trampolines<F>[claimCallbackSlot(value)];
  else throw std::invalid_argument("crossbind: a JS function cannot stand in for a variadic C callback");
}
inline bool releaseCallback(const emscripten::val &function) {
  for (std::optional<emscripten::val> &slot : callbackSlots()) {
    if (slot && slot->strictlyEquals(function)) {
      slot.reset();
      return true;
    }
  }
  return false;
}
#endif
template<typename T> constexpr bool isPassedByAddress = !IsComplete<T>::value || std::is_class_v<T> || std::is_union_v<T>;
template<typename T> struct IsSharedPtr : std::false_type {};
template<typename T> struct IsSharedPtr<std::shared_ptr<T>> : std::true_type {};
template<typename W, typename = void> struct Dereferenced {};
template<typename W> struct Dereferenced<W, std::void_t<decltype(*std::declval<const W &>())>> {
  using type = std::remove_cv_t<std::remove_reference_t<decltype(*std::declval<const W &>())>>;
};
template<typename W, bool = IsComplete<W>::value && std::is_class_v<W>> struct WrapperPointee {};
template<typename W> struct WrapperPointee<W, true> : Dereferenced<W> {};
template<typename W, typename = void> constexpr bool isSharedWrapper = false;
template<typename W> constexpr bool isSharedWrapper<W, std::void_t<typename WrapperPointee<W>::type>> = !IsSharedPtr<W>::value && std::is_convertible_v<const W &, std::shared_ptr<typename WrapperPointee<W>::type>>;
template<typename W> using SharedOf = std::shared_ptr<typename WrapperPointee<W>::type>;
template<typename W> SharedOf<W> sharedOf(const W &wrapper) { return wrapper; }
template<typename V> constexpr bool isSharedWrapperVector = false;
template<typename T, typename A> constexpr bool isSharedWrapperVector<std::vector<T, A>> = isSharedWrapper<T>;
template<typename V> std::vector<SharedOf<typename V::value_type>> sharedVector(const V &values) {
  std::vector<SharedOf<typename V::value_type>> shared;
  shared.reserve(values.size());
  for (const auto &value : values) shared.push_back(sharedOf(value));
  return shared;
}
template<typename Q, typename = void> struct JsRefOf { using type = std::conditional_t<isPassedByAddress<std::remove_cv_t<Q>>, JsPointer<Q>, std::remove_cv_t<Q>>; };
template<typename Q> struct JsRefOf<Q, std::enable_if_t<std::is_const_v<Q> && isSharedWrapper<std::remove_cv_t<Q>> && std::is_constructible_v<std::remove_cv_t<Q>, const SharedOf<std::remove_cv_t<Q>> &>>> { using type = SharedOf<std::remove_cv_t<Q>>; };
template<typename Q> using JsRef = typename JsRefOf<Q>::type;
template<typename T> using JsArg = std::conditional_t<isFunctionPointer<T>, JsCallback<T>, std::conditional_t<std::is_pointer_v<T>, JsStructPointer<std::remove_pointer_t<T>>, T>>;
template<typename Q> Q &fromJsRef(Q *p) {
  if (!p) throw std::invalid_argument("crossbind: a null pointer cannot be passed as a reference");
  return *p;
}
template<typename Q> Q &fromJsRef(const PointerHandle &p) { return fromJsRef<Q>(fromJs<Q>(p)); }
template<typename Q> Q &fromJsRef(std::remove_cv_t<Q> &value) { return value; }
template<typename Q> std::remove_cv_t<Q> fromJsRef(const SharedOf<std::remove_cv_t<Q>> &p) {
  if (!p) throw std::invalid_argument("crossbind: a null pointer cannot be passed where a non-null pointer is required");
  return std::remove_cv_t<Q>(p);
}
template<typename T> T fromJsArg(const JsArg<T> &value) {
  if constexpr (isFunctionPointer<T>) return fromJsCallback<T>(value);
  else if constexpr (std::is_pointer_v<T>) return fromJsStruct<std::remove_pointer_t<T>>(value);
  else return value;
}
template<typename Q> auto toJsRef(Q &ref) {
  if constexpr (isSharedWrapper<std::remove_cv_t<Q>>) return sharedOf(ref);
  else if constexpr (isPassedByAddress<std::remove_cv_t<Q>>) return toJs(&ref);
  else return std::remove_cv_t<Q>(ref);
}
template<typename T> auto toJsArg(T value) {
  if constexpr (std::is_pointer_v<T>) return toHandle(value);
  else return value;
}
template<typename T, typename D> std::shared_ptr<T> movedOut(std::unique_ptr<T, D> &&value) { return std::shared_ptr<T>(std::move(value)); }
template<typename R> PointerHandle movedOut(R &&value) {
  auto owned = std::make_shared<std::decay_t<R>>(std::forward<R>(value));
  return std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(owned.get()), &pointeeTag<std::decay_t<R>>, false, owned});
}
template<typename B> struct VirtualBase : emscripten::base<B> {
  template<typename C> static C *downcast(B *p) {
    if constexpr (std::is_polymorphic_v<B>) return dynamic_cast<C *>(p);
    else return nullptr;
  }
  template<typename C> static C *(*getDowncaster())(B *) { return &downcast<C>; }
};
template<typename F> auto returned(F &&call) {
  using R = std::invoke_result_t<F &>;
  if constexpr (isSharedWrapper<R>) {
    return sharedOf(call());
  } else if constexpr (isSharedWrapperVector<R>) {
    return sharedVector(call());
  } else if constexpr (std::is_class_v<R> && !std::is_copy_constructible_v<R>) {
    std::shared_ptr<R> owned(new R(call()));
    return std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(owned.get()), &pointeeTag<R>, false, owned});
  } else {
    return call();
  }
}
inline PointerHandle ownedBytes(size_t capacity, const char *pointee) {
  std::shared_ptr<char[]> bytes(new char[capacity + 1]());
  PointerHandle p = std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(bytes.get()), pointee, false, bytes});
  p->capacity = capacity;
  return p;
}
inline size_t checkedSize(int value, const char *helper) {
  if (value < 0) throw std::invalid_argument(std::string("crossbind: ") + helper + " needs a non-negative size");
  return static_cast<size_t>(value);
}
inline size_t checkedOffset(const PointerHandle &p, const char *helper, size_t index, size_t size) {
  if (!p) throw std::invalid_argument(std::string("crossbind: ") + helper + " got a null pointer");
  bool overflows = size != 0 && index >= std::numeric_limits<size_t>::max() / size;
  if (overflows || (p->storage && (index + 1) * size > p->capacity)) throw std::out_of_range(std::string("crossbind: ") + helper + " is out of bounds");
  return index * size;
}
inline void checkWritable(const PointerHandle &p, const char *helper) {
  if (p->readOnly) throw std::invalid_argument(std::string("crossbind: ") + helper + " got a read-only pointer");
}
inline PointerHandle cstring(const std::string &text) {
  PointerHandle p = ownedBytes(text.size() + 1, &pointeeTag<char>);
  std::memcpy(reinterpret_cast<char *>(p->address), text.data(), text.size());
  return p;
}
inline PointerHandle allocBuffer(int size) { return ownedBytes(checkedSize(size, "allocBuffer"), &pointeeTag<void>); }
inline PointerHandle allocPointer(int count) {
  size_t slots = checkedSize(count, "allocPointer");
  if (slots > (std::numeric_limits<size_t>::max() - 1) / sizeof(void *)) throw std::out_of_range("crossbind: allocPointer got more slots than memory can address");
  return ownedBytes(slots * sizeof(void *), &pointeeTag<void *>);
}
inline std::string readCString(PointerHandle p) {
  if (!p) throw std::invalid_argument("crossbind: readCString got a null pointer");
  if (p->pointee != &pointeeTag<char> && p->pointee != &pointeeTag<signed char> && p->pointee != &pointeeTag<unsigned char> && p->pointee != &pointeeTag<void>) throw std::invalid_argument("crossbind: pointer type mismatch");
  return reinterpret_cast<const char *>(p->address);
}
inline PointerHandle allocString(const std::string &text) { return movedOut(std::string(text)); }
inline std::string readString(PointerHandle p) {
  if (!p) throw std::invalid_argument("crossbind: readString got a null pointer");
  if (p->pointee != &pointeeTag<std::string>) throw std::invalid_argument("crossbind: pointer type mismatch");
  return *reinterpret_cast<const std::string *>(p->address);
}
inline PointerHandle readPointerAt(PointerHandle slots, int index) {
  size_t at = checkedOffset(slots, "readPointerAt", checkedSize(index, "readPointerAt"), sizeof(void *));
  void *value = nullptr;
  std::memcpy(&value, reinterpret_cast<const char *>(slots->address) + at, sizeof(void *));
  if (!value) return nullptr;
  return std::make_shared<NativePointer>(NativePointer{reinterpret_cast<std::uintptr_t>(value), slots->element ? slots->element : &pointeeTag<void>, slots->elementReadOnly, nullptr});
}
inline void writePointerAt(PointerHandle slots, int index, PointerHandle value) {
  size_t slot = checkedSize(index, "writePointerAt");
  size_t at = checkedOffset(slots, "writePointerAt", slot, sizeof(void *));
  checkWritable(slots, "writePointerAt");
  void *address = value ? reinterpret_cast<void *>(value->address) : nullptr;
  std::memcpy(reinterpret_cast<char *>(slots->address) + at, &address, sizeof(void *));
  if (slots->storage) {
    if (slot >= slots->retained.size()) slots->retained.resize(slot + 1);
    slots->retained[slot] = value;
  }
  if (value && !slots->element) {
    slots->element = value->pointee;
    slots->elementReadOnly = value->readOnly;
  }
}
inline size_t numberSize(const std::string &kind) {
  if (kind == "int8" || kind == "uint8") return 1;
  if (kind == "int16" || kind == "uint16") return 2;
  if (kind == "int32" || kind == "uint32" || kind == "float32") return 4;
  if (kind == "int64" || kind == "uint64" || kind == "float64") return 8;
  throw std::invalid_argument("crossbind: unknown number kind " + kind);
}
template<typename T> double readAs(const char *at) {
  T value;
  std::memcpy(&value, at, sizeof(T));
  return static_cast<double>(value);
}
template<typename T> void writeAs(char *at, double number) {
  bool fits = std::is_integral_v<T> ? (number >= static_cast<double>(std::numeric_limits<T>::lowest()) && number < static_cast<double>(std::numeric_limits<T>::max()) + 1.0) : (!std::isfinite(number) || std::fabs(number) <= static_cast<double>(std::numeric_limits<T>::max()));
  if (!fits) throw std::out_of_range("crossbind: writeNumberAt got a value its kind cannot hold");
  T value = static_cast<T>(number);
  std::memcpy(at, &value, sizeof(T));
}
inline double readNumberAt(PointerHandle p, int index, const std::string &kind) {
  size_t size = numberSize(kind);
  size_t at = checkedOffset(p, "readNumberAt", checkedSize(index, "readNumberAt"), size);
  const char *bytes = reinterpret_cast<const char *>(p->address) + at;
  if (kind == "int8") return readAs<int8_t>(bytes);
  if (kind == "uint8") return readAs<uint8_t>(bytes);
  if (kind == "int16") return readAs<int16_t>(bytes);
  if (kind == "uint16") return readAs<uint16_t>(bytes);
  if (kind == "int32") return readAs<int32_t>(bytes);
  if (kind == "uint32") return readAs<uint32_t>(bytes);
  if (kind == "int64") return readAs<int64_t>(bytes);
  if (kind == "uint64") return readAs<uint64_t>(bytes);
  if (kind == "float32") return readAs<float>(bytes);
  return readAs<double>(bytes);
}
inline void writeNumberAt(PointerHandle p, int index, const std::string &kind, double number) {
  size_t size = numberSize(kind);
  size_t at = checkedOffset(p, "writeNumberAt", checkedSize(index, "writeNumberAt"), size);
  checkWritable(p, "writeNumberAt");
  char *bytes = reinterpret_cast<char *>(p->address) + at;
  if (kind == "int8") writeAs<int8_t>(bytes, number);
  else if (kind == "uint8") writeAs<uint8_t>(bytes, number);
  else if (kind == "int16") writeAs<int16_t>(bytes, number);
  else if (kind == "uint16") writeAs<uint16_t>(bytes, number);
  else if (kind == "int32") writeAs<int32_t>(bytes, number);
  else if (kind == "uint32") writeAs<uint32_t>(bytes, number);
  else if (kind == "int64") writeAs<int64_t>(bytes, number);
  else if (kind == "uint64") writeAs<uint64_t>(bytes, number);
  else if (kind == "float32") writeAs<float>(bytes, number);
  else writeAs<double>(bytes, number);
}
inline std::u16string readBytes(PointerHandle p, int length) {
  size_t size = checkedSize(length, "readBytes");
  checkedOffset(p, "readBytes", 0, size);
  const unsigned char *bytes = reinterpret_cast<const unsigned char *>(p->address);
  return std::u16string(bytes, bytes + size);
}
inline void writeBytes(PointerHandle p, const std::u16string &bytes) {
  checkedOffset(p, "writeBytes", 0, bytes.size());
  checkWritable(p, "writeBytes");
  for (char16_t unit : bytes) {
    if (unit > 0xFF) throw std::invalid_argument("crossbind: writeBytes takes one byte per character");
  }
  std::copy(bytes.begin(), bytes.end(), reinterpret_cast<unsigned char *>(p->address));
}
#ifdef __EMSCRIPTEN__
inline emscripten::val readBuffer(PointerHandle p, int length) {
  size_t size = checkedSize(length, "readBuffer");
  checkedOffset(p, "readBuffer", 0, size);
  return emscripten::val(emscripten::typed_memory_view(size, reinterpret_cast<const unsigned char *>(p->address))).call<emscripten::val>("slice");
}
inline void writeBuffer(PointerHandle p, const emscripten::val &bytes) {
  emscripten::val arrayBuffer = emscripten::val::global("ArrayBuffer");
  emscripten::val uint8Array = emscripten::val::global("Uint8Array");
  emscripten::val source = emscripten::val::undefined();
  if (bytes.instanceof(arrayBuffer)) source = uint8Array.new_(bytes);
  else if (arrayBuffer.call<bool>("isView", bytes)) source = uint8Array.new_(bytes["buffer"], bytes["byteOffset"], bytes["byteLength"]);
  else throw std::invalid_argument("crossbind: writeBuffer takes an ArrayBuffer or a view of one");
  size_t size = source["length"].as<size_t>();
  checkedOffset(p, "writeBuffer", 0, size);
  checkWritable(p, "writeBuffer");
  emscripten::val(emscripten::typed_memory_view(size, reinterpret_cast<unsigned char *>(p->address))).call<void>("set", source);
}
#else
inline facebook::jsi::Value readBuffer(PointerHandle p, int length) {
  size_t size = checkedSize(length, "readBuffer");
  checkedOffset(p, "readBuffer", 0, size);
  facebook::jsi::Runtime &runtime = *emscripten::jsRuntime;
  facebook::jsi::Object bytes = runtime.global().getPropertyAsFunction(runtime, "Uint8Array").callAsConstructor(runtime, static_cast<double>(size)).getObject(runtime);
  if (size) std::memcpy(bytes.getPropertyAsObject(runtime, "buffer").getArrayBuffer(runtime).data(runtime), reinterpret_cast<const void *>(p->address), size);
  return bytes;
}
inline void writeBuffer(PointerHandle p, const facebook::jsi::Value &bytes) {
  facebook::jsi::Runtime &runtime = *emscripten::jsRuntime;
  bool isBuffer = bytes.isObject() && bytes.getObject(runtime).isArrayBuffer(runtime);
  bool isView = !isBuffer && bytes.isObject() && runtime.global().getPropertyAsObject(runtime, "ArrayBuffer").getPropertyAsFunction(runtime, "isView").call(runtime, bytes).getBool();
  if (!isBuffer && !isView) throw std::invalid_argument("crossbind: writeBuffer takes an ArrayBuffer or a view of one");
  facebook::jsi::Object object = bytes.getObject(runtime);
  facebook::jsi::Object buffer = isBuffer ? bytes.getObject(runtime) : object.getPropertyAsObject(runtime, "buffer");
  if (!buffer.isArrayBuffer(runtime)) throw std::invalid_argument("crossbind: writeBuffer cannot read a SharedArrayBuffer");
  facebook::jsi::ArrayBuffer data = buffer.getArrayBuffer(runtime);
  size_t offset = isView ? static_cast<size_t>(object.getProperty(runtime, "byteOffset").getNumber()) : 0;
  size_t size = isView ? static_cast<size_t>(object.getProperty(runtime, "byteLength").getNumber()) : data.size(runtime);
  checkedOffset(p, "writeBuffer", 0, size);
  checkWritable(p, "writeBuffer");
  if (size) std::memcpy(reinterpret_cast<void *>(p->address), data.data(runtime) + offset, size);
}
#endif
inline void registerPointerRuntime() {
  emscripten::class_<NativePointer>("NativePointer").smart_ptr<PointerHandle>("NativePointer");
  emscripten::function("cstring", &cstring);
  emscripten::function("allocBuffer", &allocBuffer);
  emscripten::function("allocPointer", &allocPointer);
  emscripten::function("readCString", &readCString);
  emscripten::function("readPointerAt", &readPointerAt);
  emscripten::function("writePointerAt", &writePointerAt);
  emscripten::function("readNumberAt", &readNumberAt);
  emscripten::function("writeNumberAt", &writeNumberAt);
  emscripten::function("readBytes", &readBytes);
  emscripten::function("writeBytes", &writeBytes);
  emscripten::function("readBuffer", &readBuffer);
  emscripten::function("writeBuffer", &writeBuffer);
  emscripten::function("releaseCallback", &releaseCallback);
  emscripten::function("allocString", &allocString);
  emscripten::function("readString", &readString);
}
inline emscripten::internal::InitFunc pointerRuntimeInit(registerPointerRuntime);
}
