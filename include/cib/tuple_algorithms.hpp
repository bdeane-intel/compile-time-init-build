#pragma once

#include <cib/tuple.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <iterator>
#include <utility>

namespace cib {

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
        return T{std::move(outer_tuple)[index<element_indices[Is].outer>]
                                       [index<element_indices[Is].inner>]...};
    }
    (std::make_index_sequence<total_num_elements>{});
}

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
            return R{std::forward<T>(t)[index<indices[Js]>]...};
        }
        (std::make_index_sequence<num_matches>{});
    }
    (std::make_index_sequence<tuple_size_v<tuple_t>>{});
}

namespace detail {
template <std::size_t I, typename... Ts>
constexpr auto invoke_at(auto &&op, Ts &&...ts) -> decltype(auto) {
    return op(std::forward<Ts>(ts)[index<I>]...);
}
} // namespace detail

template <template <typename> typename... Fs, typename Op, typename T,
          typename... Ts>
constexpr auto transform(Op &&op, T &&t, Ts &&...ts) {
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        if constexpr (sizeof...(Fs) == 0) {
            return tuple{detail::invoke_at<Is>(op, std::forward<T>(t),
                                               std::forward<Ts>(ts)...)...};
        } else {
            return make_indexed_tuple<Fs...>(detail::invoke_at<Is>(
                op, std::forward<T>(t), std::forward<Ts>(ts)...)...);
        }
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});
}

template <typename Op, typename T>
constexpr auto apply(Op &&op, T &&t) -> decltype(auto) {
    return std::forward<T>(t).apply(std::forward<Op>(op));
}

template <typename Op, typename T, typename... Ts>
constexpr auto for_each(Op &&op, T &&t, Ts &&...ts) -> Op {
    [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        (detail::invoke_at<Is>(op, std::forward<T>(t), std::forward<Ts>(ts)...),
         ...);
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});
    return op;
}

template <typename F, typename T, typename... Ts>
constexpr auto all_of(F &&f, T &&t, Ts &&...ts) -> bool {
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        return (... and detail::invoke_at<Is>(f, std::forward<T>(t),
                                              std::forward<Ts>(ts)...));
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});
}

template <typename F, typename T, typename... Ts>
constexpr auto any_of(F &&f, T &&t, Ts &&...ts) -> bool {
    return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
        return (... or detail::invoke_at<Is>(f, std::forward<T>(t),
                                             std::forward<Ts>(ts)...));
    }
    (std::make_index_sequence<tuple_size_v<std::remove_cvref_t<T>>>{});
}

template <typename... Ts> constexpr auto none_of(Ts &&...ts) -> bool {
    return not any_of(std::forward<Ts>(ts)...);
}

} // namespace cib
