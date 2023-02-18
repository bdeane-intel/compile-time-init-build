#pragma once

#include <cib/detail/compiler.hpp>
#include <cib/tuple.hpp>
#include <cib/tuple_algorithms.hpp>

#include <limits>
#include <type_traits>

namespace interrupt {
enum class resource_status { OFF = 0, ON = 1 };

template <typename T, typename = void> constexpr auto has_enable_field = false;
template <typename T>
constexpr auto has_enable_field<T, std::void_t<decltype(T::enable_field)>> =
    true;

template <typename RootT, typename ConcurrencyPolicyT>
struct dynamic_controller {
  private:
    /**
     * Store the interrupt enable values that are allowed given the current set
     * of resources that are available.
     *
     * @tparam RegType
     *      The croo::Register this mask corresponds to.
     */
    template <typename RegType>
    CIB_CONSTINIT static inline typename RegType::DataType allowed_enables =
        std::numeric_limits<typename RegType::DataType>::max();

    /**
     * For each ResourceType, keep track of what interrupts can still be enabled
     * when that resource goes down.
     *
     * Each bit in this mask corresponds to an interrupt enable field in
     * RegType. If the bit is '1', that means the corresponding interrupt can be
     * enabled when the resource is not available. If the bit is '0', that means
     * the corresonding interrupt must be disabled when the resource is not
     * available.
     *
     * @tparam ResourceType
     *      The resource we want to check.
     *
     * @tparam RegType
     *      The specific register mask we want to check.
     */
    template <typename ResourceType, typename RegType>
    constexpr static typename RegType::DataType irqs_allowed = []() {
        // get all interrupt enable fields that don't require the given resource
        auto const matching_irqs = cib::filter(RootT::all_irqs, [](auto irq) {
            using irq_t = typename decltype(irq)::type;
            constexpr auto doesnt_require_resource = cib::apply(
                [](auto... resources_pack) {
                    return (not std::is_same_v<decltype(resources_pack),
                                               ResourceType> and
                            ...);
                },
                irq_t::resources);
            return doesnt_require_resource and has_enable_field<irq_t>;
        });

        auto const interrupt_enables_tuple = cib::transform(
            [](auto irq) { return irq.enable_field; }, matching_irqs);

        // filter fields that aren't in RegType
        auto const fields_in_reg =
            cib::filter(interrupt_enables_tuple, [](auto field) {
                using FieldsRegType =
                    typename decltype(field)::type::RegisterType;
                return std::is_same_v<FieldsRegType, RegType>;
            });

        // set the bits in the mask for interrupts that don't require the
        // resource
        using DataType = typename RegType::DataType;
        return fields_in_reg.fold_left(
            DataType{}, [](DataType value, auto field) -> DataType {
                return value | field.get_mask();
            });
    }();

    template <typename ResourceType>
    CIB_CONSTINIT static inline bool is_resource_on = true;

    template <typename RegTypeTuple>
    static inline void reprogram_interrupt_enables(RegTypeTuple regs) {
        cib::for_each(
            [](auto reg) {
                using RegType = decltype(reg);

                // make sure we don't enable any interrupts that are not allowed
                // according to resource availability
                auto const final_enables =
                    allowed_enables<RegType> & dynamic_enables<RegType>;

                // update the hardware registers
                apply(write(reg.raw(final_enables)));
            },
            regs);
    }

    template <typename RegFieldTuple>
    constexpr static auto get_unique_regs(RegFieldTuple fields) {
        return fields.fold_left(cib::make_tuple(), [](auto regs, auto field) {
            constexpr bool reg_has_been_seen_already = cib::apply(
                [=](auto... regs_pack) {
                    return (
                        std::is_same_v<typename decltype(field)::RegisterType,
                                       decltype(regs_pack)> ||
                        ...);
                },
                decltype(regs){});

            if constexpr (reg_has_been_seen_already) {
                return regs;
            } else {
                return cib::tuple_cat(regs,
                                      cib::make_tuple(field.get_register()));
            }
        });
    }

    /**
     * tuple of every resource mentioned in the interrupt configuration
     */
    constexpr static auto all_resources = RootT::all_irqs.fold_left(
        cib::make_tuple(), [](auto resources, auto irq) {
            // TODO: check that an IRQ doesn't list a resource more than once
            auto const additional_resources =
                cib::filter(irq.resources, [=](auto resource) {
                    using resource_t = typename decltype(resource)::type;
                    return not cib::apply(
                        [](auto... resources_pack) {
                            return (std::is_same_v<resource_t,
                                                   decltype(resources_pack)> or
                                    ...);
                        },
                        resources);
                });
            return cib::tuple_cat(resources, additional_resources);
        });

    /**
     * tuple of every interrupt register affected by a resource
     */
    constexpr static auto all_resource_affected_regs =
        get_unique_regs(RootT::all_irqs.fold_left(
            cib::make_tuple(), [](auto registers, auto irq) {
                using irq_t = decltype(irq);
                constexpr bool depends_on_resources =
                    irq_t::resources.size() > 0u;
                if constexpr (has_enable_field<irq_t> && depends_on_resources) {
                    return cib::tuple_cat(
                        registers,
                        cib::make_tuple(irq.enable_field.get_register()));
                } else {
                    return registers;
                }
            }));

    /**
     * Reprogram interrupt enables based on updated resource availability.
     */
    static inline auto recalculate_allowed_enables() {
        // set allowed_enables mask for each resource affected register
        cib::for_each(
            [](auto reg) {
                using RegType = decltype(reg);
                using DataType = typename RegType::DataType;
                allowed_enables<RegType> = std::numeric_limits<DataType>::max();
            },
            all_resource_affected_regs);

        // for each resource, if it is not on, mask out unavailable interrupts
        cib::for_each(
            [=](auto resource) {
                using ResourceType = decltype(resource);
                if (not is_resource_on<ResourceType>) {
                    cib::for_each(
                        [](auto reg) {
                            using RegType = decltype(reg);
                            allowed_enables<RegType> &=
                                irqs_allowed<ResourceType, RegType>;
                        },
                        all_resource_affected_regs);
                }
            },
            all_resources);

        return all_resource_affected_regs;
    }

    /**
     * Store the interrupt enable values that FW _wants_ at runtime,
     * irrespective of any resource conflicts that would require specific
     * interrupts to be disabled.
     *
     * @tparam RegType
     *      The croo::Register this value corresponds to.
     */
    template <typename RegType>
    CIB_CONSTINIT static inline typename RegType::DataType dynamic_enables{};

    template <bool en, typename... CallbacksToFind>
    static inline void enable_by_name() {
        // NOTE: critical section is not needed here because shared state is
        // only updated by the final call to enable_by_field

        // TODO: add support to enable/disable top-level IRQs by name.
        //       this will require another way to manage them vs. mmio
        //       registers. once that goes in, then enable_by_field should be
        //       removed or made private.
        auto const matching_irqs = cib::filter(RootT::all_irqs, [](auto irq) {
            using irq_t = typename decltype(irq)::type;
            using IrqCallbackType = typename irq_t::IrqCallbackType;
            constexpr auto has_callback =
                (std::is_same_v<CallbacksToFind, IrqCallbackType> or ...);
            return has_callback and has_enable_field<irq_t>;
        });

        auto const interrupt_enables_tuple = cib::transform(
            [](auto irq) { return irq.enable_field; }, matching_irqs);

        cib::apply(
            [](auto... fields) { enable_by_field<en, decltype(fields)...>(); },
            interrupt_enables_tuple);
    }

  public:
    template <typename ResourceType>
    static inline void update_resource(resource_status status) {
        ConcurrencyPolicyT::call_in_critical_section([&] {
            is_resource_on<ResourceType> = (status == resource_status::ON);
            recalculate_allowed_enables();
            reprogram_interrupt_enables(all_resource_affected_regs);
        });
    }

    template <typename ResourceType> static inline void turn_on_resource() {
        update_resource<ResourceType>(resource_status::ON);
    }

    template <typename ResourceType> static inline void turn_off_resource() {
        update_resource<ResourceType>(resource_status::OFF);
    }

    template <bool en, typename... FieldsToSet>
    static inline void enable_by_field() {
        auto const interrupt_enables_tuple = cib::tuple<FieldsToSet...>{};

        ConcurrencyPolicyT::call_in_critical_section([&] {
            // update the dynamic enables
            if constexpr (en) {
                cib::for_each(
                    [](auto f) {
                        using RegType = decltype(f.get_register());
                        dynamic_enables<RegType> |= f.get_mask();
                    },
                    interrupt_enables_tuple);
            } else {
                cib::for_each(
                    [](auto f) {
                        using RegType = decltype(f.get_register());
                        dynamic_enables<RegType> &= ~f.get_mask();
                    },
                    interrupt_enables_tuple);
            }

            auto const unique_regs = get_unique_regs(interrupt_enables_tuple);
            reprogram_interrupt_enables(unique_regs);
        });
    }

    template <typename... CallbacksToFind> static inline void enable() {
        enable_by_name<true, CallbacksToFind...>();
    }

    template <typename... CallbacksToFind> static inline void disable() {
        enable_by_name<false, CallbacksToFind...>();
    }
};
} // namespace interrupt
