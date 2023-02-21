#pragma once

#include <cstddef>
#include <iterator>
#include <type_traits>
#include <utility>

namespace cib {
template <std::size_t I>
using index_constant = std::integral_constant<std::size_t, I>;
template <std::size_t I> constexpr auto index = index_constant<I>{};

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
template <std::size_t Index, typename T, template <typename> typename... Fs>
struct element {
    [[nodiscard]] constexpr auto get(index_constant<Index>) const &noexcept
        -> T const & {
        return t;
    }
    [[nodiscard]] constexpr auto get(index_constant<Index>) &noexcept -> T & {
        return t;
    }
    [[nodiscard]] constexpr auto get(index_constant<Index>) &&noexcept -> T && {
        return std::forward<T>(t);
    }

    template <typename U>
        requires(std::is_same_v<U, T> or ... or
                 std::is_same_v<U, Fs<std::remove_cvref_t<T>>>)
    [[nodiscard]] constexpr auto get(std::type_identity<U>) const &noexcept
        -> T const & {
        return t;
    }
    template <typename U>
        requires(std::is_same_v<U, T> or ... or
                 std::is_same_v<U, Fs<std::remove_cvref_t<T>>>)
    [[nodiscard]] constexpr auto get(std::type_identity<U>) &noexcept -> T & {
        return t;
    }
    template <typename U>
        requires(std::is_same_v<U, T> or ... or
                 std::is_same_v<U, Fs<std::remove_cvref_t<T>>>)
    [[nodiscard]] constexpr auto get(std::type_identity<U>) &&noexcept -> T && {
        return std::forward<T>(t);
    }

    [[nodiscard]] constexpr auto value(index_constant<Index>) && -> T;

    T t;

  private:
    [[nodiscard]] friend constexpr auto operator==(element const &,
                                                   element const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto operator<=>(element const &,
                                                    element const &) = default;
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

template <std::size_t... Is, template <typename> typename... Fs, typename... Ts>
struct tuple_impl<std::index_sequence<Is...>, index_function_list<Fs...>, Ts...>
    : private element<Is, Ts, Fs...>... {
    using element<Is, Ts, Fs...>::get...;
    using element<Is, Ts, Fs...>::value...;

    constexpr tuple_impl() = default;
    template <typename... Us>
    constexpr explicit(true) tuple_impl(Us &&...us) noexcept
        : element<Is, Ts, Fs...>{std::forward<Us>(us)}... {}

    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_left(Init &&init,
                                                  Op &&op) const & {
        return (fold_helper{op, std::forward<Init>(init)} + ... +
                get(index<Is>))
            .value;
    }
    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_left(Init &&init, Op &&op) && {
        return (fold_helper{op, std::forward<Init>(init)} + ... +
                std::move(*this).get(index<Is>))
            .value;
    }

    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_right(Init &&init,
                                                   Op &&op) const & {
        return (get(index<Is>) + ... +
                fold_helper{op, std::forward<Init>(init)})
            .value;
    }
    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_right(Init &&init, Op &&op) && {
        return (std::move(*this).get(index<Is>) + ... +
                fold_helper{op, std::forward<Init>(init)})
            .value;
    }

    template <std::size_t I>
    constexpr auto operator[](index_constant<I> i) const & -> decltype(auto) {
        return get(i);
    }
    template <std::size_t I>
    constexpr auto operator[](index_constant<I> i) & -> decltype(auto) {
        return get(i);
    }
    template <std::size_t I>
    constexpr auto operator[](index_constant<I> i) && -> decltype(auto) {
        return std::move(*this).get(i);
    }

  private:
    [[nodiscard]] friend constexpr auto operator==(tuple_impl const &,
                                                   tuple_impl const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto
    operator<=>(tuple_impl const &, tuple_impl const &) = default;
};

template <typename... Ts> struct failed_size {
    template <typename...> static constexpr auto always_false = false;
    static_assert(always_false<Ts...>, "Could not get tuple_size_v for type");
    static constexpr auto value = 0;
};
} // namespace detail

template <typename... Ts>
constexpr std::size_t tuple_size_v = detail::failed_size<Ts...>::value;
template <std::size_t, typename> struct tuple_element;
template <std::size_t I, typename T>
using tuple_element_t = typename tuple_element<I, T>::type;

template <typename IndexList, typename... Ts>
struct indexed_tuple
    : detail::tuple_impl<std::index_sequence_for<Ts...>, IndexList, Ts...> {
    using detail::tuple_impl<std::index_sequence_for<Ts...>, IndexList,
                             Ts...>::tuple_impl;

    static constexpr auto size() -> std::size_t { return sizeof...(Ts); }

  private:
    [[nodiscard]] friend constexpr auto operator==(indexed_tuple const &,
                                                   indexed_tuple const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto
    operator<=>(indexed_tuple const &, indexed_tuple const &) = default;
};

template <typename... Ts>
indexed_tuple(Ts...) -> indexed_tuple<detail::index_function_list<>, Ts...>;

template <typename... Ts>
constexpr std::size_t tuple_size_v<indexed_tuple<Ts...>> = sizeof...(Ts) - 1;

template <std::size_t I, typename... Ts>
struct tuple_element<I, indexed_tuple<Ts...>> {
    using type = decltype(std::declval<indexed_tuple<Ts...>>().value(index<I>));
};

#if __cpp_deduction_guides < 201907L
template <typename... Ts>
struct tuple : detail::tuple_impl<std::index_sequence_for<Ts...>,
                                  detail::index_function_list<>, Ts...> {
    using detail::tuple_impl<std::index_sequence_for<Ts...>,
                             detail::index_function_list<>, Ts...>::tuple_impl;

    static constexpr auto size() -> std::size_t { return sizeof...(Ts); }

  private:
    [[nodiscard]] friend constexpr auto operator==(tuple const &, tuple const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto operator<=>(tuple const &,
                                                    tuple const &) = default;
};
template <typename... Ts> tuple(Ts...) -> tuple<Ts...>;

template <typename... Ts>
constexpr std::size_t tuple_size_v<tuple<Ts...>> = sizeof...(Ts);

template <std::size_t I, typename... Ts> struct tuple_element<I, tuple<Ts...>> {
    using type = decltype(std::declval<tuple<Ts...>>().value(index<I>));
};
#else
template <typename... Ts>
using tuple = indexed_tuple<detail::index_function_list<>, Ts...>;
#endif

template <std::size_t I, typename Tuple>
[[nodiscard]] constexpr auto get(Tuple &&t)
    -> decltype(std::forward<Tuple>(t).get(index<I>)) {
    return std::forward<Tuple>(t).get(index<I>);
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
