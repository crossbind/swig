#include <set>
#include <string>
#include <type_traits>
#include <typeinfo>

namespace crossbind {
inline bool claimRegistration(const std::string &key) {
  static std::set<std::string> claimed;
  return claimed.insert(key).second;
}
inline bool claimType(const std::type_info &type, const char *name) {
  return claimRegistration(std::string("type ") + type.name()) && claimRegistration(std::string("name ") + name);
}
inline bool claimFunction(const char *name, int arity) {
  return claimRegistration(std::string("function ") + name + "/" + std::to_string(arity));
}
template<typename M> struct MemberOf;
template<typename C, typename T> struct MemberOf<T C::*> { using Class = C; using Type = T; };
template<typename T> constexpr bool isFieldNumber = std::is_arithmetic_v<T> && !std::is_same_v<T, long double>
  && !std::is_same_v<T, wchar_t> && !std::is_same_v<T, char16_t> && !std::is_same_v<T, char32_t>;
template<auto M, bool Instance, typename Builder> void bindPointerField(const Builder &cls, const char *name);
template<auto M, bool Instance, typename Builder> void bindField(const Builder &cls, const char *name) {
  using C = typename MemberOf<decltype(M)>::Class;
  using T = typename MemberOf<decltype(M)>::Type;
  using U = std::remove_cv_t<T>;
  if constexpr (isFieldNumber<U> || std::is_same_v<U, std::string>) {
    cls.property(name, M);
  } else if constexpr (std::is_enum_v<U>) {
    using I = std::underlying_type_t<U>;
    if constexpr (std::is_const_v<T>) cls.property(name, +[](const C &s) { return static_cast<I>(s.*M); });
    else cls.property(name, +[](const C &s) { return static_cast<I>(s.*M); }, +[](C &s, I v) { s.*M = static_cast<U>(v); });
  } else if constexpr (std::is_pointer_v<U> && !std::is_function_v<std::remove_pointer_t<U>>) {
    bindPointerField<M, Instance>(cls, name);
  }
}
template<typename T> void bindConstant(const char *name, const T &value) {
  using U = std::decay_t<T>;
  [[maybe_unused]] auto claim = [name] { return claimRegistration(std::string("name ") + name); };
  if constexpr (std::is_same_v<U, char *> || std::is_same_v<U, const char *>) { if (value && claim()) emscripten::constant(name, std::string(value)); }
  else if constexpr (std::is_same_v<U, bool>) { if (claim()) emscripten::constant(name, value); }
  else if constexpr (std::is_enum_v<U>) { if (claim()) emscripten::constant(name, static_cast<double>(static_cast<std::underlying_type_t<U>>(value))); }
  else if constexpr (std::is_arithmetic_v<U>) { if (claim()) emscripten::constant(name, static_cast<double>(value)); }
}
}

