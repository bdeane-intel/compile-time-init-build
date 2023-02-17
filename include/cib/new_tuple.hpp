#pragma once

#include <algorithm>
#include <array>
#include <concepts>
#include <cstddef>
#include <type_traits>
#include <utility>

namespace cib {
namespace detail {
template <std::size_t Index, typename T, template <typename> typename... Fs>
struct element {
    [[nodiscard]] constexpr auto
    get(std::integral_constant<std::size_t, Index>) const &noexcept
        -> T const & {
        return t;
    }
    [[nodiscard]] constexpr auto
    get(std::integral_constant<std::size_t, Index>) &noexcept -> T & {
        return t;
    }
    [[nodiscard]] constexpr auto
    get(std::integral_constant<std::size_t, Index>) &&noexcept -> T && {
        return std::forward<T>(t);
    }

    template <typename U>
        requires(std::same_as<U, T> or ... or
                 std::same_as<U, Fs<std::remove_cvref_t<T>>>)
    [[nodiscard]] constexpr auto get(std::type_identity<U>) const &noexcept
        -> T const & {
        return t;
    }
    template <typename U>
        requires(std::same_as<U, T> or ... or
                 std::same_as<U, Fs<std::remove_cvref_t<T>>>)
    [[nodiscard]] constexpr auto get(std::type_identity<U>) &noexcept -> T & {
        return t;
    }
    template <typename U>
        requires(std::same_as<U, T> or ... or
                 std::same_as<U, Fs<std::remove_cvref_t<T>>>)
    [[nodiscard]] constexpr auto get(std::type_identity<U>) &&noexcept -> T && {
        return std::forward<T>(t);
    }

    [[nodiscard]] constexpr auto
    value(std::integral_constant<std::size_t, Index>) && -> T;

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
        requires((... and std::constructible_from<Ts, Us>))
    constexpr explicit(true) tuple_impl(Us &&...us) noexcept
        : element<Is, Ts, Fs...>{std::forward<Us>(us)}... {}

    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_left(Init &&init,
                                                  Op &&op) const & {
        return (fold_helper{op, std::forward<Init>(init)} + ... +
                get(std::integral_constant<std::size_t, Is>{}))
            .value;
    }
    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_left(Init &&init, Op &&op) && {
        return (fold_helper{op, std::forward<Init>(init)} + ... +
                std::move(*this).get(std::integral_constant<std::size_t, Is>{}))
            .value;
    }

    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_right(Init &&init,
                                                   Op &&op) const & {
        return (get(std::integral_constant<std::size_t, Is>{}) + ... +
                fold_helper{op, std::forward<Init>(init)})
            .value;
    }
    template <typename Init, typename Op>
    [[nodiscard]] constexpr inline auto fold_right(Init &&init, Op &&op) && {
        return (std::move(*this).get(
                    std::integral_constant<std::size_t, Is>{}) +
                ... + fold_helper{op, std::forward<Init>(init)})
            .value;
    }

    template <std::size_t I>
    constexpr auto operator[](
        std::integral_constant<std::size_t, I> i) const & -> decltype(auto) {
        return get(i);
    }
    template <std::size_t I>
    constexpr auto
    operator[](std::integral_constant<std::size_t, I> i) & -> decltype(auto) {
        return get(i);
    }
    template <std::size_t I>
    constexpr auto
    operator[](std::integral_constant<std::size_t, I> i) && -> decltype(auto) {
        return std::move(*this).get(i);
    }

  private:
    [[nodiscard]] friend constexpr auto operator==(tuple_impl const &,
                                                   tuple_impl const &)
        -> bool = default;
    [[nodiscard]] friend constexpr auto
    operator<=>(tuple_impl const &, tuple_impl const &) = default;
};
} // namespace detail

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
#else
template <typename... Ts>
indexed_tuple(Ts...) -> indexed_tuple<detail::index_function_list<>, Ts...>;

template <typename... Ts>
using tuple = indexed_tuple<detail::index_function_list<>, Ts...>;
#endif

template <std::size_t I, typename Tuple>
[[nodiscard]] constexpr auto get(Tuple &&t)
    -> decltype(std::forward<Tuple>(t).get(
        std::integral_constant<std::size_t, I>{})) {
    return std::forward<Tuple>(t).get(std::integral_constant<std::size_t, I>{});
}

template <typename T, typename Tuple>
[[nodiscard]] constexpr auto get(Tuple &&t)
    -> decltype(std::forward<Tuple>(t).get(std::type_identity<T>{})) {
    return std::forward<Tuple>(t).get(std::type_identity<T>{});
}

template <typename...> constexpr std::size_t tuple_size_v = 0;
template <typename... Ts>
constexpr std::size_t tuple_size_v<tuple<Ts...>> = sizeof...(Ts);

template <std::size_t, typename> struct tuple_element;
template <std::size_t I, typename... Ts> struct tuple_element<I, tuple<Ts...>> {
    using type = decltype(std::declval<tuple<Ts...>>().value(
        std::integral_constant<std::size_t, I>{}));
};
template <std::size_t I, typename T>
using tuple_element_t = typename tuple_element<I, T>::type;

template <typename Op, typename T, typename... Ts>
constexpr auto transform(Op &&op, T &&t, Ts &&...ts) {
    const auto invoke_at =
        [&]<std::size_t I>(auto &&...args) -> decltype(auto) {
        return op(get<I>(std::forward<decltype(args)>(args))...);
    };

    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        return tuple{invoke_at.template operator()<Is>(
            std::forward<T>(t), std::forward<Ts>(ts)...)...};
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});
}

template <typename Op, typename T>
constexpr auto apply(Op &&op, T &&t) -> decltype(auto) {
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        return std::forward<Op>(op)(get<Is>(std::forward<T>(t))...);
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});
}

template <typename Op, typename T, typename... Ts>
constexpr auto for_each(Op &&op, T &&t, Ts &&...ts) -> Op {
    const auto invoke_at = [&]<std::size_t I>(auto &&...args) -> void {
        op(get<I>(std::forward<decltype(args)>(args))...);
    };

    [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        (invoke_at.template operator()<Is>(std::forward<T>(t),
                                           std::forward<Ts>(ts)...),
         ...);
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});

    return op;
}

template <typename... Ts> constexpr auto tuple_cat(Ts &&...ts) {
    struct index_pair {
        std::size_t outer;
        std::size_t inner;
    };

    constexpr auto total_num_elements =
        (0 + ... + tuple_size_v<std::remove_cvref_t<Ts>>);
    [[maybe_unused]] constexpr auto element_indices = [&] {
        std::array<index_pair, total_num_elements> indices{};
        auto it = std::begin(indices);
        std::size_t outer{};
        [[maybe_unused]] const auto fill_indices = [&](std::size_t n) {
            std::size_t inner{};
            it = std::generate_n(it, n, [&] {
                return index_pair{outer, inner++};
            });
            ++outer;
        };
        (fill_indices(tuple_size_v<std::remove_cvref_t<Ts>>), ...);
        return indices;
    }();

    [[maybe_unused]] auto outer_tuple =
        cib::tuple<Ts &&...>{std::forward<Ts>(ts)...};
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        using T = cib::tuple<tuple_element_t<
            element_indices[Is].inner,
            std::remove_cvref_t<tuple_element_t<element_indices[Is].outer,
                                                decltype(outer_tuple)>>>...>;
        return T{get<element_indices[Is].inner>(
            get<element_indices[Is].outer>(std::move(outer_tuple)))...};
    }
    (std::make_index_sequence<total_num_elements>{});
}

template <typename...> struct show_type;

template <template <typename T> typename Pred, typename T>
[[nodiscard]] constexpr auto filter(T &&t) {
    using tuple_t = std::remove_cvref_t<T>;
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        constexpr auto num_matches =
            (std::size_t{} + ... +
             (Pred<tuple_element_t<Is, tuple_t>>::value ? std::size_t{1}
                                                        : std::size_t{}));
        constexpr auto indices = [] {
            auto a = std::array<std::size_t, num_matches>{};
            [[maybe_unused]] auto it = std::begin(a);
            auto copy_index = [&]<std::size_t I, typename Elem> {
                if constexpr (Pred<Elem>::value) {
                    *it++ = I;
                }
            };
            (copy_index.template operator()<Is, tuple_element_t<Is, tuple_t>>(),
             ...);
            return a;
        }();

        return [&]<std::size_t... Js>(std::index_sequence<Js...>) {
            using R = cib::tuple<tuple_element_t<indices[Js], tuple_t>...>;
            return R{get<indices[Js]>(std::forward<T>(t))...};
        }
        (std::make_index_sequence<num_matches>{});
    }
    (std::make_index_sequence<tuple_size_v<tuple_t>>{});
}

template <typename... Ts> [[nodiscard]] constexpr auto make_tuple(Ts &&...ts) {
    return tuple{std::forward<Ts>(ts)...};
}

template <template <typename> typename... Fs>
constexpr auto make_indexed_tuple = []<typename... Ts>(Ts &&...ts) {
    return indexed_tuple<detail::index_function_list<Fs...>, Ts...>{
        std::forward<Ts>(ts)...};
};

} // namespace cib
