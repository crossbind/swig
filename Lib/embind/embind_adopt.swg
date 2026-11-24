
#include <memory>
#include <type_traits>

namespace crossbind {
template<typename T> std::shared_ptr<T> adopt(T *made) {
  if constexpr (std::is_destructible_v<T>) return std::shared_ptr<T>(made);
  else return std::shared_ptr<T>(made, [](T *) {});
}
}
