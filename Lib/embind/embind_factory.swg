
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>

namespace crossbind {
template<typename T, typename... A> std::shared_ptr<T> makeShared(A... args) {
  if constexpr (std::is_constructible_v<T, A...>) return std::make_shared<T>(std::forward<A>(args)...);
  else throw std::invalid_argument("crossbind: this class cannot be constructed from these arguments");
}
}
