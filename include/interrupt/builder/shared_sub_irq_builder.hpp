#pragma once

#include <interrupt/builder/sub_irq_builder.hpp>
#include <interrupt/impl/shared_sub_irq_impl.hpp>

#include <boost/hana.hpp>

#include <type_traits>

namespace interrupt {
template <typename ConfigT> struct shared_sub_irq_builder {
    constexpr static auto resources = ConfigT::resources;
    using IrqCallbackType = typename ConfigT::IrqCallbackType;
    constexpr static auto children = ConfigT::children;

    constexpr static auto irqs_type =
        boost::hana::transform(ConfigT::children, [](auto child) {
            if constexpr (boost::hana::size(child.children) >
                          boost::hana::size_c<0>) {
                return shared_sub_irq_builder<decltype(child)>{};
            } else {
                return sub_irq_builder<decltype(child)>{};
            }
        });

    std::remove_cv_t<decltype(irqs_type)> irqs;

    template <typename IrqType, typename T>
    void constexpr add(T const &flow_description) {
        boost::hana::for_each(irqs, [&](auto &irq) {
            irq.template add<IrqType>(flow_description);
        });
    }

    template <typename BuilderValue, typename Index> struct sub_value {
        constexpr static auto const &value = BuilderValue::value.irqs[Index{}];
    };

    /**
     * @return shared_irq::impl specialization optimized for size and runtime.
     */
    template <typename BuilderValue>
    [[nodiscard]] auto constexpr build() const {
        using namespace boost;
        auto constexpr builder = BuilderValue::value;

        auto constexpr irq_indices = hana::to<hana::tuple_tag>(
            hana::make_range(hana::int_c<0>, hana::size(builder.irqs)));

        auto const sub_irq_impls = hana::transform(irq_indices, [&](auto i) {
            constexpr auto irq = builder.irqs[i];
            return irq.template build<sub_value<BuilderValue, decltype(i)>>();
        });

        return hana::unpack(sub_irq_impls, [](auto... sub_irq_impl_args) {
            return shared_sub_irq_impl<ConfigT, decltype(sub_irq_impl_args)...>(
                sub_irq_impl_args...);
        });
    }
};
} // namespace interrupt
