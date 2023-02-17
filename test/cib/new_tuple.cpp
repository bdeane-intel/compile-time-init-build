#include <cib/new_tuple.hpp>

#include <catch2/catch_template_test_macros.hpp>
#include <catch2/catch_test_macros.hpp>

#include <type_traits>
#include <utility>

TEST_CASE("empty tuple", "[tuple]") {
    static_assert(std::is_empty_v<cib::tuple<>>);
    constexpr auto t = cib::tuple{};
    using T = std::remove_const_t<decltype(t)>;
    static_assert(std::is_same_v<T, cib::tuple<>>);
    static_assert(cib::tuple_size_v<T> == 0);
    static_assert(T::size() == 0);
}

TEST_CASE("single element tuple", "[tuple]") {
    constexpr auto t = cib::tuple{1};
    using T = std::remove_const_t<decltype(t)>;
    static_assert(std::is_same_v<T, cib::tuple<int>>);
    static_assert(cib::tuple_size_v<T> == 1);
    static_assert(T::size() == 1);
    static_assert(sizeof(T) == sizeof(int));

    auto x = 1;
    auto u = cib::tuple{x};
    using U = decltype(u);
    static_assert(std::is_same_v<U, cib::tuple<int>>);
    static_assert(cib::tuple_size_v<U> == 1);
    static_assert(U::size() == 1);
    static_assert(sizeof(U) == sizeof(int));
}

TEST_CASE("multi element tuple", "[tuple]") {
    constexpr auto t = cib::tuple{1, 2.0f};
    using T = std::remove_const_t<decltype(t)>;
    static_assert(std::is_same_v<T, cib::tuple<int, float>>);
    static_assert(cib::tuple_size_v<T> == 2);
    static_assert(T::size() == 2);
}

TEST_CASE("constexpr tuple of references", "[tuple]") {
    static constexpr int x = 1;
    constexpr auto t = cib::tuple<int const &>{x};
    using T = std::remove_const_t<decltype(t)>;
    static_assert(cib::tuple_size_v<T> == 1);
    static_assert(T::size() == 1);
}

TEST_CASE("free get", "[tuple]") {
    constexpr auto t = cib::tuple{5, true, 10l};

    REQUIRE(cib::get<0>(t) == 5);
    REQUIRE(cib::get<1>(t) == true);
    REQUIRE(cib::get<2>(t) == 10);
    static_assert(cib::get<0>(t) == 5);
    static_assert(cib::get<1>(t) == true);
    static_assert(cib::get<2>(t) == 10);

    REQUIRE(cib::get<int>(t) == 5);
    REQUIRE(cib::get<bool>(t) == true);
    REQUIRE(cib::get<long>(t) == 10);
    static_assert(cib::get<int>(t) == 5);
    static_assert(cib::get<bool>(t) == true);
    static_assert(cib::get<long>(t) == 10);
}

TEST_CASE("free get value categories", "[tuple]") {
    {
        auto const t = cib::tuple{42};
        static_assert(std::is_same_v<decltype(cib::get<0>(t)), int const &>);
        static_assert(std::is_same_v<decltype(cib::get<int>(t)), int const &>);
    }
    {
        auto t = cib::tuple{42};
        static_assert(std::is_same_v<decltype(cib::get<0>(t)), int &>);
        static_assert(std::is_same_v<decltype(cib::get<int>(t)), int &>);
        static_assert(
            std::is_same_v<decltype(cib::get<0>(std::move(t))), int &&>);
        static_assert(
            std::is_same_v<decltype(cib::get<int>(std::move(t))), int &&>);
    }
}

template <char... Chars>
    requires(... and (Chars >= '0' and Chars <= '9'))
consteval auto operator""_idx() {
    constexpr auto n = [] {
        auto x = std::size_t{};
        ((x *= 10, x += Chars - '0'), ...);
        return x;
    }();
    return std::integral_constant<std::size_t, n>{};
}

TEST_CASE("indexing", "[tuple]") {
    constexpr auto t = cib::tuple{5, true, 10l};
    static_assert(t[0_idx] == 5);
    static_assert(t[1_idx] == true);
    static_assert(t[2_idx] == 10l);

    static_assert(std::is_same_v<decltype(t[0_idx]), int const &>);
    auto u = cib::tuple{1};
    static_assert(std::is_same_v<decltype(u[0_idx]), int &>);
    static_assert(std::is_same_v<decltype(cib::tuple{1}[0_idx]), int &&>);
}

TEST_CASE("tuple of lvalue references", "[tuple]") {
    auto x = 1;
    auto t = cib::tuple<int &>{x};
    CHECK(cib::get<0>(t) == 1);
    cib::get<0>(t) = 2;
    CHECK(cib::get<0>(t) == 2);
    CHECK(x == 2);
}

TEST_CASE("tuple size/elements", "[tuple]") {
    using T = cib::tuple<int, bool>;
    static_assert(cib::tuple_size_v<T> == 2);
    static_assert(std::is_same_v<cib::tuple_element_t<0, T>, int>);
    static_assert(std::is_same_v<cib::tuple_element_t<1, T>, bool>);

    using A = cib::tuple<int &>;
    static_assert(std::is_same_v<cib::tuple_element_t<0, A>, int &>);
    using B = cib::tuple<int const &>;
    static_assert(std::is_same_v<cib::tuple_element_t<0, B>, int const &>);
    using C = cib::tuple<int &&>;
    static_assert(std::is_same_v<cib::tuple_element_t<0, C>, int &&>);
}

namespace {
struct A {};
struct B {
    B(int) {}
};
} // namespace

TEST_CASE("default constructability", "[tuple]") {
    static_assert(std::is_default_constructible_v<cib::tuple<A>>);
    static_assert(std::is_nothrow_default_constructible_v<cib::tuple<A>>);
    static_assert(not std::is_default_constructible_v<cib::tuple<B>>);
    static_assert(not std::is_nothrow_default_constructible_v<cib::tuple<B>>);
}

TEMPLATE_TEST_CASE("constructability", "[tuple]",
                   (cib::detail::element<0, int>), cib::tuple<>,
                   (cib::tuple<A, int, bool>)) {
    static_assert(std::is_default_constructible_v<TestType>);
    static_assert(std::is_nothrow_default_constructible_v<TestType>);
}

TEMPLATE_TEST_CASE("copyability", "[tuple]", (cib::detail::element<0, int>),
                   cib::tuple<>, (cib::tuple<A, int, bool>)) {
    static_assert(std::is_copy_constructible_v<TestType>);
    static_assert(std::is_copy_assignable_v<TestType>);
    static_assert(std::is_nothrow_copy_constructible_v<TestType>);
    static_assert(std::is_nothrow_copy_assignable_v<TestType>);
    static_assert(std::is_trivially_copy_constructible_v<TestType>);
    static_assert(std::is_trivially_copy_assignable_v<TestType>);
}

TEMPLATE_TEST_CASE("moveability", "[tuple]", (cib::detail::element<0, int>),
                   cib::tuple<>, (cib::tuple<A, int, bool>)) {
    static_assert(std::is_move_constructible_v<TestType>);
    static_assert(std::is_move_assignable_v<TestType>);
    static_assert(std::is_nothrow_move_constructible_v<TestType>);
    static_assert(std::is_nothrow_move_assignable_v<TestType>);
    static_assert(std::is_trivially_move_constructible_v<TestType>);
    static_assert(std::is_trivially_move_assignable_v<TestType>);
}

TEMPLATE_TEST_CASE("destructability", "[tuple]", (cib::detail::element<0, int>),
                   cib::tuple<>, (cib::tuple<A, int, bool>)) {
    static_assert(std::is_nothrow_destructible_v<TestType>);
    static_assert(std::is_trivially_destructible_v<TestType>);
}

struct move_only {
    constexpr move_only() = default;
    constexpr move_only(int i) : value{i} {}
    constexpr move_only(move_only &&) = default;
    constexpr auto operator=(move_only &&) noexcept -> move_only & = default;

    friend constexpr auto operator==(move_only const &lhs, move_only const &rhs)
        -> bool {
        return lhs.value == rhs.value;
    }

    int value{};
};

TEST_CASE("move-only types", "[tuple]") {
    static_assert(std::is_default_constructible_v<cib::tuple<move_only>>);
    static_assert(
        std::is_nothrow_default_constructible_v<cib::tuple<move_only>>);

    static_assert(not std::is_copy_constructible_v<cib::tuple<move_only>>);
    static_assert(not std::is_copy_assignable_v<cib::tuple<move_only>>);

    static_assert(std::is_move_constructible_v<cib::tuple<move_only>>);
    static_assert(std::is_move_assignable_v<cib::tuple<move_only>>);
    static_assert(std::is_nothrow_move_constructible_v<cib::tuple<move_only>>);
    static_assert(std::is_nothrow_move_assignable_v<cib::tuple<move_only>>);
    static_assert(
        std::is_trivially_move_constructible_v<cib::tuple<move_only>>);
    static_assert(std::is_trivially_move_assignable_v<cib::tuple<move_only>>);

    static_assert(std::is_nothrow_destructible_v<cib::tuple<move_only>>);
    static_assert(std::is_trivially_destructible_v<cib::tuple<move_only>>);
}

TEST_CASE("equality comparable", "[tuple]") {
    constexpr auto t = cib::tuple{5, 10};

    REQUIRE(t == t);
    REQUIRE(t != cib::tuple{5, 11});
    static_assert(t == t); // NOLINT(misc-redundant-expression)
    static_assert(t != cib::tuple{5, 11});
}

TEST_CASE("order comparable", "[tuple]") {
    constexpr auto t = cib::tuple{5, 10};

    REQUIRE(t < cib::tuple{6, 9});
    REQUIRE(t < cib::tuple{5, 11});
    REQUIRE(not(t < t));
    REQUIRE(not(t < cib::tuple{4, 11}));
    static_assert(t < cib::tuple{6, 9});
    static_assert(t < cib::tuple{5, 11});
    static_assert(not(t < t)); // NOLINT(misc-redundant-expression)
    static_assert(not(t < cib::tuple{4, 11}));

    REQUIRE(t <= t);
    REQUIRE(t <= cib::tuple{6, 9});
    REQUIRE(t <= cib::tuple{5, 11});
    REQUIRE(not(t <= cib::tuple{5, 9}));
    REQUIRE(not(t <= cib::tuple{4, 11}));
    static_assert(t <= t); // NOLINT(misc-redundant-expression)
    static_assert(t <= cib::tuple{6, 9});
    static_assert(t <= cib::tuple{5, 11});
    static_assert(not(t <= cib::tuple{5, 9}));
    static_assert(not(t <= cib::tuple{4, 11}));

    REQUIRE(t > cib::tuple{5, 9});
    REQUIRE(t > cib::tuple{4, 11});
    REQUIRE(not(t > t));
    REQUIRE(not(t > cib::tuple{6, 9}));
    static_assert(t > cib::tuple{5, 9});
    static_assert(t > cib::tuple{4, 11});
    static_assert(not(t > t)); // NOLINT(misc-redundant-expression)
    static_assert(not(t > cib::tuple{6, 9}));

    REQUIRE(t >= t);
    REQUIRE(t >= cib::tuple{5, 9});
    REQUIRE(t >= cib::tuple{4, 11});
    REQUIRE(not(t >= cib::tuple{5, 11}));
    REQUIRE(not(t >= cib::tuple{6, 9}));
    static_assert(t >= t); // NOLINT(misc-redundant-expression)
    static_assert(t >= cib::tuple{5, 9});
    static_assert(t >= cib::tuple{4, 11});
    static_assert(not(t >= cib::tuple{5, 11}));
    static_assert(not(t >= cib::tuple{6, 9}));
}

TEST_CASE("spaceship comparable", "[tuple]") {
    constexpr auto t = cib::tuple{5, 10};

    REQUIRE(t <=> t == std::strong_ordering::equal);
    REQUIRE(t <=> cib::tuple{6, 9} == std::strong_ordering::less);
    REQUIRE(t <=> cib::tuple{6, 10} == std::strong_ordering::less);
    REQUIRE(t <=> cib::tuple{5, 11} == std::strong_ordering::less);
    REQUIRE(t <=> cib::tuple{5, 9} == std::strong_ordering::greater);
    REQUIRE(t <=> cib::tuple{4, 10} == std::strong_ordering::greater);
    REQUIRE(t <=> cib::tuple{4, 11} == std::strong_ordering::greater);
    static_assert(t <=> t == std::strong_ordering::equal);
    static_assert(t <=> cib::tuple{6, 9} == std::strong_ordering::less);
    static_assert(t <=> cib::tuple{6, 10} == std::strong_ordering::less);
    static_assert(t <=> cib::tuple{5, 11} == std::strong_ordering::less);
    static_assert(t <=> cib::tuple{5, 9} == std::strong_ordering::greater);
    static_assert(t <=> cib::tuple{4, 10} == std::strong_ordering::greater);
    static_assert(t <=> cib::tuple{4, 11} == std::strong_ordering::greater);
}

TEST_CASE("unary transform", "[tuple]") {
    static_assert(transform([](auto) { return 1; }, cib::tuple{}) ==
                  cib::tuple{});
    constexpr auto t = cib::tuple{1, 2, 3};
    constexpr auto u = transform([](auto x) { return x + 1; }, t);
    static_assert(u == cib::tuple{2, 3, 4});
}

TEST_CASE("n-ary transform", "[tuple]") {
    static_assert(transform([](auto, auto) { return 1; }, cib::tuple{},
                            cib::tuple{}) == cib::tuple{});
    constexpr auto t = cib::tuple{1, 2, 3};
    constexpr auto u = transform([](auto x, auto y) { return x + y; }, t, t);
    static_assert(u == cib::tuple{2, 4, 6});
}

TEST_CASE("rvalue transform", "[tuple]") {
    auto t = cib::tuple{1, 2, 3};
    const auto u = transform([](int &&x) { return x + 1; }, std::move(t));
    CHECK(u == cib::tuple{2, 3, 4});
}

TEST_CASE("free get is SFINAE-friendly", "[tuple]") {
    constexpr auto empty = cib::tuple{};
    constexpr auto t = cib::transform(
        [&](auto... args) {
            return cib::tuple{cib::get<decltype(args)>(empty)...};
        },
        cib::tuple{});
    static_assert(t == cib::tuple{});
}

TEST_CASE("apply", "[tuple]") {
    static_assert(
        apply([](auto... xs) { return (0 + ... + xs); }, cib::tuple{}) == 0);
    static_assert(apply([](auto... xs) { return (0 + ... + xs); },
                        cib::tuple{1, 2, 3}) == 6);

    auto stateful = [calls = 0](auto...) mutable { return ++calls; };
    CHECK(apply(stateful, cib::tuple{1, 2, 3}) == 1);
    CHECK(apply(stateful, cib::tuple{1, 2, 3}) == 2);

    static_assert(
        apply([](auto x) { return x.value; }, cib::tuple{move_only{42}}) == 42);

    auto t = cib::tuple{1, 2, 3};
    apply([](auto &...xs) { (++xs, ...); }, t);
    CHECK(t == cib::tuple{2, 3, 4});
}

TEST_CASE("for_each (free function)", "[tuple]") {
    {
        const auto t = cib::tuple{};
        auto sum = 0;
        for_each([&](auto x, auto y) { sum += x + y; }, t, t);
        CHECK(sum == 0);
    }
    {
        const auto t = cib::tuple{1, 2, 3};
        auto sum = 0;
        for_each([&](auto x, auto y) { sum += x + y; }, t, t);
        CHECK(sum == 12);
    }
    {
        const auto t = cib::tuple{1};
        auto sum = 0;
        for_each([&](auto x, auto &&y) { sum += x + y.value; }, t,
                 cib::tuple{move_only{2}});
        CHECK(sum == 3);
    }
    {
        auto const t = cib::tuple{1, 2, 3};
        auto f = for_each(
            [calls = 0](auto) mutable {
                ++calls;
                return calls;
            },
            t);
        CHECK(f(0) == 4);
    }
}

TEST_CASE("tuple_cat", "[tuple]") {
    static_assert(cib::tuple_cat() == cib::tuple{});
    static_assert(tuple_cat(cib::tuple{}, cib::tuple{}) == cib::tuple{});
    static_assert(tuple_cat(cib::tuple{1, 2}, cib::tuple{}) ==
                  cib::tuple{1, 2});
    static_assert(tuple_cat(cib::tuple{}, cib::tuple{1, 2}) ==
                  cib::tuple{1, 2});
    static_assert(tuple_cat(cib::tuple{1, 2}, cib::tuple{3, 4}) ==
                  cib::tuple{1, 2, 3, 4});
    static_assert(tuple_cat(cib::tuple{1, 2}, cib::tuple{3, 4},
                            cib::tuple{5, 6}) == cib::tuple{1, 2, 3, 4, 5, 6});
    static_assert(tuple_cat(cib::tuple{1, 2}, cib::tuple{}, cib::tuple{3, 4}) ==
                  cib::tuple{1, 2, 3, 4});

    auto t = tuple_cat(cib::tuple{1}, cib::tuple{2});
    static_assert(std::is_same_v<decltype(t), cib::tuple<int, int>>);
}

TEST_CASE("tuple_cat (move only)", "[tuple]") {
    auto t = tuple_cat(cib::tuple{move_only{5}}, cib::tuple{move_only{10}});
    static_assert(
        std::is_same_v<decltype(t), cib::tuple<move_only, move_only>>);
    CHECK(t == cib::tuple{move_only{5}, move_only{10}});
}

TEST_CASE("tuple_cat (references)", "[tuple]") {
    auto x = 1;
    auto t = tuple_cat(cib::tuple<int &>{x}, cib::tuple<int &>{x});
    static_assert(std::is_same_v<decltype(t), cib::tuple<int &, int &>>);
    get<0>(t) = 2;
    CHECK(x == 2);
    get<1>(t) = 1;
    CHECK(x == 1);
}

TEST_CASE("tuple_cat (const references)", "[tuple]") {
    auto x = 1;
    auto t = tuple_cat(cib::tuple<int const &>{x}, cib::tuple<int const &>{x});
    static_assert(
        std::is_same_v<decltype(t), cib::tuple<int const &, int const &>>);
    x = 2;
    CHECK(get<0>(t) == 2);
    CHECK(get<1>(t) == 2);
}

TEST_CASE("tuple_cat (rvalue references)", "[tuple]") {
    auto x = 1;
    auto y = 2;
    auto t = tuple_cat(cib::tuple<int &&>{std::move(x)},
                       cib::tuple<int &&>{std::move(y)});
    static_assert(std::is_same_v<decltype(t), cib::tuple<int &&, int &&>>);
    x = 2;
    CHECK(get<0>(t) == 2);
    y = 2;
    CHECK(get<1>(t) == 2);
}

TEST_CASE("fold_left", "[tuple]") {
    constexpr auto t = cib::tuple{1, 2, 3};
    static_assert(t.fold_left(0, std::minus{}) == (((0 - 1) - 2) - 3));
    static_assert(cib::tuple{move_only{1}, move_only{2}, move_only{3}}
                      .fold_left(move_only{0},
                                 [](move_only &&x, move_only &&y) {
                                     return move_only{x.value + y.value};
                                 })
                      .value == 6);

    int calls{};
    auto stateful = [&](auto x, auto y) mutable {
        ++calls;
        return x + y;
    };
    CHECK(t.fold_left(0, stateful) == 6);
    CHECK(calls == 3);
}

TEST_CASE("fold_left (heterogeneous types in fold)", "[tuple]") {
    constexpr auto t = cib::tuple{1, 2, 3};
    static_assert(t.fold_left(cib::tuple{}, [](auto acc, auto n) {
        return tuple_cat(acc, cib::tuple{n});
    }) == t);

    static_assert(
        cib::tuple{1, 2, 3}.fold_left(cib::tuple{}, [](auto acc, auto n) {
            return cib::tuple_cat(acc, cib::tuple{n});
        }) == t);
}

template <auto N> struct addend {
    constexpr friend auto operator==(addend, addend) -> bool { return true; }
};
template <auto X, auto Y> constexpr auto operator+(addend<X>, addend<Y>) {
    return addend<X + Y>{};
}

TEST_CASE("fold_left (heterogeneous types in tuple)", "[tuple]") {
    constexpr auto t = cib::tuple{addend<1>{}, addend<2>{}};
    static_assert(t.fold_left(addend<0>{}, std::plus{}) == addend<3>{});
}

TEST_CASE("fold_right", "[tuple]") {
    constexpr auto t = cib::tuple{1, 2, 3};
    static_assert(t.fold_right(4, std::minus{}) == (1 - (2 - (3 - 4))));
    static_assert(cib::tuple{move_only{1}, move_only{2}, move_only{3}}
                      .fold_right(move_only{0},
                                  [](move_only &&x, move_only &&y) {
                                      return move_only{x.value + y.value};
                                  })
                      .value == 6);

    int calls{};
    auto stateful = [&](auto x, auto y) mutable {
        ++calls;
        return x + y;
    };
    CHECK(t.fold_right(0, stateful) == 6);
    CHECK(calls == 3);
}

TEST_CASE("fold_right (heterogeneous types in fold)", "[tuple]") {
    constexpr auto t = cib::tuple{1, 2, 3};
    static_assert(t.fold_right(cib::tuple{}, [](auto n, auto acc) {
        return tuple_cat(cib::tuple{n}, acc);
    }) == t);

    static_assert(
        cib::tuple{1, 2, 3}.fold_right(cib::tuple{}, [](auto n, auto acc) {
            return cib::tuple_cat(cib::tuple{n}, acc);
        }) == t);
}

TEST_CASE("fold_right (heterogeneous types in tuple)", "[tuple]") {
    constexpr auto t = cib::tuple{addend<1>{}, addend<2>{}};
    static_assert(t.fold_right(addend<0>{}, std::plus{}) == addend<3>{});
}

template <typename T> struct is_even {
    static constexpr auto value = T::value % 2 == 0;
};

TEST_CASE("filter", "[tuple]") {
    constexpr auto t = cib::tuple{
        std::integral_constant<int, 1>{}, std::integral_constant<int, 2>{},
        std::integral_constant<int, 3>{}, std::integral_constant<int, 4>{}};
    constexpr auto u = filter<is_even>(t);
    static_assert(u == cib::tuple{std::integral_constant<int, 2>{},
                                  std::integral_constant<int, 4>{}});
}

struct counter {
    counter() = default;
    counter(counter const &) { ++copies; }
    counter(counter &&) { ++moves; }
    auto operator=(counter const &) -> counter & {
        ++copies;
        return *this;
    }
    auto operator=(counter &&) -> counter & {
        ++moves;
        return *this;
    }

    static auto reset() -> void {
        copies = 0;
        moves = 0;
    }
    static inline int copies{};
    static inline int moves{};
};

TEST_CASE("copy/move behavior for tuple", "[tuple]") {
    counter::reset();
    auto t1 = cib::tuple{counter{}};
    CHECK(counter::moves == 1);
    CHECK(counter::copies == 0);

    [[maybe_unused]] auto t2 = t1;
    CHECK(counter::moves == 1);
    CHECK(counter::copies == 1);

    [[maybe_unused]] auto t3 = std::move(t1);
    CHECK(counter::moves == 2);
    CHECK(counter::copies == 1);

    t1 = cib::tuple{counter{}};
    CHECK(counter::moves == 4);
    CHECK(counter::copies == 1);
}

TEST_CASE("copy/move behavior for tuple_cat", "[tuple]") {
    auto t1 = cib::tuple{counter{}};
    auto t2 = cib::tuple{counter{}};

    counter::reset();
    [[maybe_unused]] auto t3 = tuple_cat(t1, t2);
    CHECK(counter::moves == 0);
    CHECK(counter::copies == 2);

    [[maybe_unused]] auto t4 = tuple_cat(std::move(t1), std::move(t2));
    CHECK(counter::moves == 2);
    CHECK(counter::copies == 2);
}

template <typename> using always_true = std::true_type;

TEST_CASE("copy/move behavior for filter", "[tuple]") {
    auto t1 = cib::tuple{counter{}};

    counter::reset();
    [[maybe_unused]] auto t2 = filter<always_true>(t1);
    CHECK(counter::moves == 0);
    CHECK(counter::copies == 1);

    [[maybe_unused]] auto t3 = filter<always_true>(std::move(t1));
    CHECK(counter::moves == 1);
    CHECK(counter::copies == 1);
}

template <typename Key, typename Value> struct map_entry {
    using key_t = Key;
    using value_t = Value;

    value_t value;
};

template <typename T> using key_for = typename T::key_t;

TEST_CASE("make_tuple", "[tuple]") {
    static_assert(cib::make_tuple() == cib::tuple{});
    static_assert(cib::make_tuple(1, 2, 3) == cib::tuple{1, 2, 3});
}

TEST_CASE("make_indexed_tuple", "[tuple]") {
    static_assert(cib::make_indexed_tuple<>() == cib::tuple{});
    static_assert(cib::make_indexed_tuple<>(1, 2, 3) == cib::tuple{1, 2, 3});
}

TEST_CASE("tuple with user index", "[tuple]") {
    struct X;
    struct Y;
    constexpr auto t = cib::make_indexed_tuple<key_for>(map_entry<X, int>{42},
                                                        map_entry<Y, int>{17});
    static_assert(cib::get<X>(t).value == 42);
    static_assert(cib::get<Y>(t).value == 17);
}

template <typename Key1, typename Key2, typename Value> struct multimap_entry {
    using key1_t = Key1;
    using key2_t = Key2;
    using value_t = Value;

    value_t value;
};

template <typename T> using key1_for = typename T::key1_t;
template <typename T> using key2_for = typename T::key2_t;

TEST_CASE("tuple with multiple user indices", "[tuple]") {
    struct M;
    struct N;
    struct X;
    struct Y;
    constexpr auto t = cib::make_indexed_tuple<key1_for, key2_for>(
        multimap_entry<M, X, int>{42}, multimap_entry<N, Y, int>{17});
    static_assert(cib::get<M>(t).value == 42);
    static_assert(cib::get<X>(t).value == 42);
    static_assert(cib::get<N>(t).value == 17);
    static_assert(cib::get<Y>(t).value == 17);
}
