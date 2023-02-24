#pragma once

#include <array>
#include <cstddef>
#include <iterator>
#include <type_traits>
#include <utility>

namespace cib {
template <std::size_t I>
using index_constant = std::integral_constant<std::size_t, I>;
template <std::size_t I> static constexpr index_constant<I> index{};

namespace tuple_literals {
template <char... Chars>
    requires(... and (Chars >= '0' and Chars <= '9'))
consteval auto operator""_idx() {
    constexpr auto n = [] {
        auto x = std::size_t{};
        ((x *= 10, x += Chars - '0'), ...);
        return x;
    }();
    return index<n>;
}
} // namespace tuple_literals

namespace detail {
template <std::size_t, typename...> struct element;

template <typename T>
concept derivable = std::is_class_v<T>;
template <typename T>
concept nonderivable = not
std::is_class_v<T>;

template <std::size_t Index, nonderivable T, typename... Ts>
struct element<Index, T, Ts...> {
    [[nodiscard]] constexpr auto
    ugly_iGet_clvr(index_constant<Index>) const &noexcept -> T const & {
        return value;
    }
    [[nodiscard]] constexpr auto ugly_iGet_lvr(index_constant<Index>) &noexcept
        -> T & {
        return value;
    }
    [[nodiscard]] constexpr auto ugly_iGet_rvr(index_constant<Index>) &&noexcept
        -> T && {
        return std::forward<T>(value);
    }

    template <typename U>
        requires(std::is_same_v<U, T> or ... or std::is_same_v<U, Ts>)
    [[nodiscard]] constexpr auto ugly_tGet_clvr(
        std::type_identity<U>) const &noexcept -> T const & {
        return value;
    }
    template <typename U>
        requires(std::is_same_v<U, T> or ... or std::is_same_v<U, Ts>)
    [[nodiscard]] constexpr auto ugly_tGet_lvr(std::type_identity<U>) &noexcept
        -> T & {
        return value;
    }
    template <typename U>
        requires(std::is_same_v<U, T> or ... or std::is_same_v<U, Ts>)
    [[nodiscard]] constexpr auto ugly_tGet_rvr(std::type_identity<U>) &&noexcept
        -> T && {
        return std::forward<T>(value);
    }

    static constexpr auto ugly_Value(index_constant<Index>) -> T;

    T value;

  private:
    [[nodiscard]] friend constexpr auto operator==(element const &,
                                                   element const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto operator<=>(element const &,
                                                    element const &) = default;
};

template <std::size_t Index, derivable T, typename... Ts>
struct element<Index, T, Ts...> : T {
    static constexpr auto ugly_Index = Index;

    [[nodiscard]] constexpr auto
    ugly_iGet_clvr(index_constant<Index>) const &noexcept -> T const & {
        return *this;
    }
    [[nodiscard]] constexpr auto ugly_iGet_lvr(index_constant<Index>) &noexcept
        -> T & {
        return *this;
    }
    [[nodiscard]] constexpr auto ugly_iGet_rvr(index_constant<Index>) &&noexcept
        -> T && {
        return std::move(*this);
    }

    template <typename U>
        requires(std::is_same_v<U, T> or ... or std::is_same_v<U, Ts>)
    [[nodiscard]] constexpr auto ugly_tGet_clvr(
        std::type_identity<U>) const &noexcept -> T const & {
        return *this;
    }
    template <typename U>
        requires(std::is_same_v<U, T> or ... or std::is_same_v<U, Ts>)
    [[nodiscard]] constexpr auto ugly_tGet_lvr(std::type_identity<U>) &noexcept
        -> T & {
        return *this;
    }
    template <typename U>
        requires(std::is_same_v<U, T> or ... or std::is_same_v<U, Ts>)
    [[nodiscard]] constexpr auto ugly_tGet_rvr(std::type_identity<U>) &&noexcept
        -> T && {
        return std::move(*this);
    }

    static constexpr auto ugly_Value(index_constant<Index>) -> T;
};

template <typename Op, typename Value> struct fold_helper {
    Op &op;
    Value value;

  private:
    template <typename Rhs>
    friend constexpr auto operator+(fold_helper &&lhs, Rhs &&rhs) {
        using R =
            decltype(lhs.op(std::move(lhs).value, std::forward<Rhs>(rhs)));
        return fold_helper<Op, std::remove_cvref_t<R>>{
            lhs.op, lhs.op(std::move(lhs).value, std::forward<Rhs>(rhs))};
    }

    template <typename Lhs>
    friend constexpr auto operator+(Lhs &&lhs, fold_helper &&rhs) {
        using R =
            decltype(rhs.op(std::forward<Lhs>(lhs), std::move(rhs).value));
        return fold_helper<Op, std::remove_cvref_t<R>>{
            rhs.op, rhs.op(std::forward<Lhs>(lhs), std::move(rhs).value)};
    }
};

template <typename Op, typename Value>
fold_helper(Op, Value) -> fold_helper<Op, std::remove_cvref_t<Value>>;

template <template <typename> typename...> struct index_function_list {};
template <typename...> struct tuple_impl;

template <template <typename> typename... Fs> struct element_helper {
    template <std::size_t I, typename T>
    using element_t = element<I, T, Fs<std::remove_cvref_t<T>>...>;
};

struct index_pair {
    std::size_t outer;
    std::size_t inner;
};

template <std::size_t... Is, template <typename> typename... Fs, typename... Ts>
struct tuple_impl<std::index_sequence<Is...>, index_function_list<Fs...>, Ts...>
    : element_helper<Fs...>::template element_t<Is, Ts>... {
  private:
    template <std::size_t I, typename T>
    using base_t = typename element_helper<Fs...>::template element_t<I, T>;

  public:
    using base_t<Is, Ts>::ugly_iGet_clvr...;
    using base_t<Is, Ts>::ugly_iGet_lvr...;
    using base_t<Is, Ts>::ugly_iGet_rvr...;
    using base_t<Is, Ts>::ugly_tGet_clvr...;
    using base_t<Is, Ts>::ugly_tGet_lvr...;
    using base_t<Is, Ts>::ugly_tGet_rvr...;
    using base_t<Is, Ts>::ugly_Value...;

    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_left(Init &&init,
                                                  Op &&op) const & {
        return (fold_helper{op, std::forward<Init>(init)} + ... +
                ugly_iGet_clvr(index<Is>))
            .value;
    }
    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_left(Init &&init, Op &&op) && {
        return (fold_helper{op, std::forward<Init>(init)} + ... +
                std::move(*this).ugly_iGet_rvr(index<Is>))
            .value;
    }

    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_right(Init &&init,
                                                   Op &&op) const & {
        return (ugly_iGet_clvr(index<Is>) + ... +
                fold_helper{op, std::forward<Init>(init)})
            .value;
    }
    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_right(Init &&init, Op &&op) && {
        return (std::move(*this).ugly_iGet_rvr(index<Is>) + ... +
                fold_helper{op, std::forward<Init>(init)})
            .value;
    }

    template <std::size_t I>
    [[nodiscard]] constexpr auto
    operator[](index_constant<I> i) const & -> decltype(auto) {
        return ugly_iGet_clvr(i);
    }
    template <std::size_t I>
    [[nodiscard]] constexpr auto
    operator[](index_constant<I> i) & -> decltype(auto) {
        return ugly_iGet_lvr(i);
    }
    template <std::size_t I>
    [[nodiscard]] constexpr auto
    operator[](index_constant<I> i) && -> decltype(auto) {
        return std::move(*this).ugly_iGet_rvr(i);
    }

    [[nodiscard]] constexpr auto get(auto idx) const & -> decltype(auto) {
        return ugly_tGet_clvr(idx);
    }
    [[nodiscard]] constexpr auto get(auto idx) & -> decltype(auto) {
        return ugly_tGet_lvr(idx);
    }
    [[nodiscard]] constexpr auto get(auto idx) && -> decltype(auto) {
        return std::move(*this).ugly_tGet_rvr(idx);
    }

    template <typename Op>
    constexpr auto apply(Op &&op) const & -> decltype(auto) {
        return std::forward<Op>(op)(ugly_iGet_clvr(index<Is>)...);
    }
    template <typename Op> constexpr auto apply(Op &&op) & -> decltype(auto) {
        return std::forward<Op>(op)(ugly_iGet_lvr(index<Is>)...);
    }
    template <typename Op> constexpr auto apply(Op &&op) && -> decltype(auto) {
        return std::forward<Op>(op)(
            std::move(*this).ugly_iGet_rvr(index<Is>)...);
    }

    static constexpr auto size() -> std::size_t { return sizeof...(Ts); }
    static constexpr auto ugly_Value(...) -> void;

    [[nodiscard]] static constexpr auto fill_inner_indices(index_pair *p)
        -> index_pair * {
        ((p++->inner = Is), ...);
        return p;
    }
    [[nodiscard]] static constexpr auto
    fill_outer_indices(index_pair *p, [[maybe_unused]] std::size_t n)
        -> index_pair * {
        ((p++->outer = (static_cast<void>(Is), n)), ...);
        return p;
    }

  private:
    [[nodiscard]] friend constexpr auto operator==(tuple_impl const &,
                                                   tuple_impl const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto
    operator<=>(tuple_impl const &, tuple_impl const &) = default;
};

template <typename... Ts>
tuple_impl(Ts...)
    -> tuple_impl<std::index_sequence_for<Ts...>, index_function_list<>, Ts...>;
} // namespace detail

template <typename T> constexpr auto tuple_size_v = T::size();

template <std::size_t I, typename T>
using tuple_element_t = decltype(T::ugly_Value(index<I>));

#if __cpp_deduction_guides < 201907L
template <typename... Ts>
struct tuple : detail::tuple_impl<std::index_sequence_for<Ts...>,
                                  detail::index_function_list<>, Ts...> {};
template <typename... Ts> tuple(Ts...) -> tuple<Ts...>;

template <typename IndexList, typename... Ts>
struct indexed_tuple
    : detail::tuple_impl<std::index_sequence_for<Ts...>, IndexList, Ts...> {};

template <typename... Ts>
indexed_tuple(Ts...) -> indexed_tuple<detail::index_function_list<>, Ts...>;
#else
template <typename... Ts>
using tuple = detail::tuple_impl<std::index_sequence_for<Ts...>,
                                 detail::index_function_list<>, Ts...>;

template <typename IndexList, typename... Ts>
using indexed_tuple =
    detail::tuple_impl<std::index_sequence_for<Ts...>, IndexList, Ts...>;
#endif

template <std::size_t I, typename Tuple>
[[nodiscard]] constexpr auto get(Tuple &&t)
    -> decltype(std::forward<Tuple>(t)[index<I>]) {
    return std::forward<Tuple>(t)[index<I>];
}

template <typename T, typename Tuple>
[[nodiscard]] constexpr auto get(Tuple &&t)
    -> decltype(std::forward<Tuple>(t).get(std::type_identity<T>{})) {
    return std::forward<Tuple>(t).get(std::type_identity<T>{});
}

template <typename... Ts> [[nodiscard]] constexpr auto make_tuple(Ts &&...ts) {
    return tuple<std::remove_cvref_t<Ts>...>{std::forward<Ts>(ts)...};
}

template <template <typename> typename... Fs>
constexpr auto make_indexed_tuple = []<typename... Ts>(Ts &&...ts) {
    return indexed_tuple<detail::index_function_list<Fs...>,
                         std::remove_cvref_t<Ts>...>{std::forward<Ts>(ts)...};
};

template <template <typename> typename... Fs, typename T>
constexpr auto apply_indices(T &&t) {
    using tuple_t = std::remove_cvref_t<T>;
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        return indexed_tuple<detail::index_function_list<Fs...>,
                             tuple_element_t<Is, tuple_t>...>{
            std::forward<T>(t)[index<Is>]...};
    }
    (std::make_index_sequence<tuple_size_v<tuple_t>>{});
}

} // namespace cib
