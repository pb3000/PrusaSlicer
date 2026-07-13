#include "ExtrusionOrder.hpp"

#include <algorithm>
#include <cassert>
#include <cinttypes>
#include <limits>
#include <set>

#include "libslic3r/ClipperUtils.hpp"

#include "libslic3r/GCode/SmoothPath.hpp"
#include "libslic3r/ShortestPath.hpp"
#include "libslic3r/Config.hpp"
#include "libslic3r/ExtrusionEntity.hpp"
#include "libslic3r/ExtrusionEntityCollection.hpp"
#include "libslic3r/ExtrusionRole.hpp"
#include "libslic3r/GCode/WipeTowerIntegration.hpp"
#include "libslic3r/Geometry/ArcWelder.hpp"
#include "libslic3r/LayerRegion.hpp"
#include "libslic3r/Print.hpp"

namespace Slic3r::GCode::ExtrusionOrder {

bool is_overriden(const ExtrusionEntityCollection &eec, const LayerTools &layer_tools, const std::size_t instance_id) {
    return layer_tools.wiping_extrusions().get_extruder_override(&eec, instance_id) > -1;
}

int get_extruder_id(
    const ExtrusionEntityCollection &eec,
    const LayerTools &layer_tools,
    const PrintRegion &region,
    const std::size_t instance_id
) {
    if (is_overriden(eec, layer_tools, instance_id)) {
        return layer_tools.wiping_extrusions().get_extruder_override(&eec, instance_id);
    }

    const int extruder_id = layer_tools.extruder(eec, region);
    if (! layer_tools.has_extruder(extruder_id)) {
        // Extruder is not in layer_tools - we'll print it by last extruder on this layer (could
        // happen e.g. when a wiping object is taller than others - dontcare extruders are
        // eradicated from layer_tools)
        return layer_tools.extruders.back();
    }
    return extruder_id;
}

Point get_gcode_point(const InstancePoint &point, const Point &offset) {
    return point.local_point + offset;
}

InstancePoint get_instance_point(const Point &point, const Point &offset) {
    return {point - offset};
}

std::optional<Point> get_gcode_point(const std::optional<InstancePoint> &point, const Point &offset) {
    if (point) {
        return get_gcode_point(*point, offset);
    }
    return std::nullopt;
}

std::optional<InstancePoint> get_instance_point(const std::optional<Point> &point, const Point &offset) {
    if (point) {
        return get_instance_point(*point, offset);
    }
    return std::nullopt;
}

using ExtractEntityPredicate = std::function<bool(const ExtrusionEntityCollection&, const PrintRegion&)>;

ExtrusionEntitiesPtr extract_infill_extrusions(
    const PrintRegion &region,
    const ExtrusionEntityCollection &fills,
    const LayerExtrusionRanges::const_iterator& begin,
    const LayerExtrusionRanges::const_iterator& end,
    const ExtractEntityPredicate &should_pick_extrusion
) {
    ExtrusionEntitiesPtr result;
    for (auto it = begin; it != end; ++ it) {
        assert(it->region() == begin->region());
        const LayerExtrusionRange &range{*it};
        for (uint32_t fill_id : range) {
            assert(dynamic_cast<ExtrusionEntityCollection*>(fills.entities[fill_id]));

            auto *eec{static_cast<ExtrusionEntityCollection*>(fills.entities[fill_id])};
            if (eec == nullptr || eec->empty() || !should_pick_extrusion(*eec, region)) {
                continue;
            }

            if (eec->can_reverse()) {
                // Flatten the infill collection for better path planning.
                for (auto *ee : eec->entities) {
                    result.emplace_back(ee);
                }
            } else {
                result.emplace_back(eec);
            }
        }
    }
    return result;
}

std::vector<Perimeter> extract_perimeter_extrusions(
    const Print &print,
    const Layer &layer,
    const LayerIsland &island,
    const ExtractEntityPredicate &should_pick_extrusion,
    const unsigned extruder_id,
    const Point &offset,
    std::optional<Point> &previous_position,
    const PathSmoothingFunction &smooth_path
) {
    std::vector<Perimeter> result;

    const LayerRegion &layerm = *layer.get_region(island.perimeters.region());
    const PrintRegion &region = print.get_print_region(layerm.region().print_region_id());

    for (uint32_t perimeter_id : island.perimeters) {
        // Extrusions inside islands are expected to be ordered already.
        // Don't reorder them.
        assert(dynamic_cast<ExtrusionEntityCollection*>(layerm.perimeters().entities[perimeter_id]));
        auto *eec = static_cast<ExtrusionEntityCollection*>(layerm.perimeters().entities[perimeter_id]);
        if (eec == nullptr || eec->empty() || !should_pick_extrusion(*eec, region)) {
            continue;
        }

        for (ExtrusionEntity *ee : *eec) {
            if (ee != nullptr) {
                std::optional<InstancePoint> last_position{get_instance_point(previous_position, offset)};
                bool reverse_loop{false};
                if (auto loop = dynamic_cast<const ExtrusionLoop *>(ee)) {
                    const bool is_hole = loop->is_clockwise();
                    reverse_loop = print.config().prefer_clockwise_movements ? !is_hole : is_hole;
                }
                auto [path, wipe_offset]{smooth_path(&layer, &region, ExtrusionEntityReference{*ee, reverse_loop}, extruder_id, last_position)};
                previous_position = get_gcode_point(last_position, offset);
                if (!path.empty()) {
                    result.push_back(Perimeter{std::move(path), reverse_loop, ee, wipe_offset});
                }
            }
        }
    }

    return result;
}

std::vector<ExtrusionEntityReference> sort_fill_extrusions(const ExtrusionEntitiesPtr &fills, const Point* start_near) {
    if (fills.empty()) {
        return {};
    }
    std::vector<ExtrusionEntityReference> sorted_extrusions;

    for (const ExtrusionEntityReference &fill : chain_extrusion_references(fills, start_near)) {
        if (auto *eec = dynamic_cast<const ExtrusionEntityCollection*>(&fill.extrusion_entity()); eec) {
            for (const ExtrusionEntityReference &ee : chain_extrusion_references(*eec, start_near, fill.flipped())) {
                sorted_extrusions.push_back(ee);
            }
        } else {
            sorted_extrusions.push_back(fill);
        }
    }
    return sorted_extrusions;
}

std::vector<InfillRange> extract_infill_ranges(
    const Print &print,
    const Layer &layer,
    const LayerIsland &island,
    const Point &offset,
    std::optional<Point> &previous_position,
    const ExtractEntityPredicate &should_pick_extrusion,
    const PathSmoothingFunction &smooth_path,
    const unsigned extruder_id
) {
    std::vector<InfillRange> result;
    for (auto it = island.fills.begin(); it != island.fills.end();) {
        // Gather range of fill ranges with the same region.
        auto it_end = it;
        for (++ it_end; it_end != island.fills.end() && it->region() == it_end->region(); ++ it_end) ;
        const LayerRegion &layerm = *layer.get_region(it->region());
        // PrintObjects own the PrintRegions, thus the pointer to PrintRegion would be unique to a PrintObject, they would not
        // identify the content of PrintRegion accross the whole print uniquely. Translate to a Print specific PrintRegion.
        const PrintRegion &region = print.get_print_region(layerm.region().print_region_id());

        ExtrusionEntitiesPtr extrusions{extract_infill_extrusions(
            region,
            layerm.fills(),
            it,
            it_end,
            should_pick_extrusion
        )};

        const std::optional<InstancePoint> previous_instance_point{get_instance_point(previous_position, offset)};
        const Point* start_near{previous_instance_point ? &(previous_instance_point->local_point) : nullptr};
        const ExtrusionEntityReferences sorted_extrusions{sort_fill_extrusions(extrusions, start_near)};

        std::vector<SmoothPath> paths;
        for (const ExtrusionEntityReference &extrusion_reference : sorted_extrusions) {
            std::optional<InstancePoint> last_position{get_instance_point(previous_position, offset)};
            auto [path, _]{smooth_path(&layer, &region, extrusion_reference, extruder_id, last_position)};
            if (!path.empty()) {
                paths.push_back(std::move(path));
            }
            previous_position = get_gcode_point(last_position, offset);
        }
        if (!paths.empty()) {
            result.push_back({std::move(paths), &region});
        }
        it = it_end;
    }
    return result;
}

// Returns LayerIslands ordered for printing. The order strategy controls how the first island of the
// layer is chosen relative to where the previous layer ended (see PrintConfig::island_order):
//  - Nearest:  start near the previous layer's end (shortest travel; default, original behaviour).
//  - Farthest: start at the island farthest from the previous layer's end, so the layer starts away
//              from where it just ended and the turnaround area is not printed twice back-to-back.
//  - Fixed:    ignore the previous layer's end -> deterministic, the same order on every layer.
std::vector<std::reference_wrapper<const LayerIsland>> get_ordered_islands(
    const LayerSlice &lslice,
    const std::optional<Point> &previous_position,
    const IslandOrder order
) {
    std::vector<std::reference_wrapper<const LayerIsland>> islands_to_order;
    for (const LayerIsland &island : lslice.islands) {
        islands_to_order.emplace_back(island);
    }

    const Point *seed = previous_position.has_value() ? std::addressof(*previous_position) : nullptr;
    if (order == IslandOrder::Fixed || seed == nullptr) {
        chain_and_reorder_layer_islands(islands_to_order, nullptr);
    } else if (order == IslandOrder::Farthest && islands_to_order.size() > 1) {
        // Seed the chaining from the island farthest from the previous layer's end (same per-island
        // representative point chain_layer_islands uses: boundary.contour.first_point()).
        Point  far_seed = *seed;
        double best     = -1.;
        for (const LayerIsland &island : lslice.islands) {
            const Point  p = island.boundary.contour.first_point();
            const double d = (p - *seed).cast<double>().squaredNorm();
            if (d > best) { best = d; far_seed = p; }
        }
        chain_and_reorder_layer_islands(islands_to_order, &far_seed);
    } else if (order == IslandOrder::SecondNearest && islands_to_order.size() > 1) {
        // Seed from the nearest island OTHER than the one nearest the previous layer's end, so the
        // layer starts at a different area than where it just finished, with the least extra travel.
        Point  nearest_pt = *seed;
        Point  second_pt  = *seed;
        double d1 = std::numeric_limits<double>::max();
        double d2 = std::numeric_limits<double>::max();
        for (const LayerIsland &island : lslice.islands) {
            const Point  p = island.boundary.contour.first_point();
            const double d = (p - *seed).cast<double>().squaredNorm();
            if (d < d1) { d2 = d1; second_pt = nearest_pt; d1 = d; nearest_pt = p; }
            else if (d < d2) { d2 = d; second_pt = p; }
        }
        chain_and_reorder_layer_islands(islands_to_order, &second_pt);
    } else {
        chain_and_reorder_layer_islands(islands_to_order, seed);
    }
    return islands_to_order;
}

// Asynchronous infill: a layer defers its sparse internal infill to the pass of the layer above
// (printed one layer below the walls) only if it has both a layer below and a layer above. This
// keeps the first layer, the top layer and thus bridges/top-bottom shells printed in place.
bool layer_defers_infill(const Layer &layer, const Print &print) {
    return print.config().async_infill && layer.lower_layer != nullptr && layer.upper_layer != nullptr;
}

// Asynchronous infill accessibility check (level A, all-or-nothing per region).
// def_layer's sparse infill is printed one layer up, during the pass of def_layer.upper_layer. Returns
// the set of print_region_ids of def_layer whose infill would then be covered by taller material of a
// tool printed earlier in that upper layer, so the nozzle could no longer reach it. Such regions must
// NOT be deferred (printed in place instead). The obstacle is inflated by the nozzle tip clearance
// (tip outer radius - orifice radius): the infill extrudate legitimately reaches the orifice, only the
// metal tip's overhang needs to clear. Single-tool upper layers are accessible by construction.
std::set<int> blocked_infill_regions(const Print &print, const Layer &def_layer, const ToolOrdering &tool_ordering) {
    std::set<int> blocked;
    const Layer *upper = def_layer.upper_layer;
    if (upper == nullptr)
        return blocked;
    const LayerTools &upper_tools = tool_ordering.tools_for_layer(upper->print_z);
    if (upper_tools.extruders.size() <= 1)
        return blocked; // single tool: nothing of a different tool can cover the infill

    const double tip_outer = print.config().nozzle_tip_outer_diameter.value;

    for (size_t r = 0; r < def_layer.region_count(); ++ r) {
        const LayerRegion *rl = def_layer.get_region(int(r));
        // Test against the fillable area (inset from the slice boundary by the perimeters), not the
        // whole region footprint - otherwise an adjacent earlier-tool region inflated by the tip
        // clearance clips the perimeter band and falsely blocks a region whose infill is well clear.
        if (rl == nullptr || rl->fill_expolygons().empty())
            continue;
        const int infill_tool     = rl->region().config().infill_extruder.value; // 1-based
        const int infill_print_id = rl->region().print_region_id();

        const double nozzle_inner = print.config().nozzle_diameter.get_at(std::max(0, infill_tool - 1));
        const double clearance    = std::max(0., (tip_outer - nozzle_inner) / 2.);

        // Order-independent: block if the infill is covered on the layer above by material of a
        // DIFFERENT tool, regardless of the per-layer alternating tool order. Using the tool order
        // here would flicker the decision between layers (infill printed "two layers at once"); the
        // geometric coverage by another tool is what matters and is stable across layers.
        Polygons obstacle;
        for (size_t q = 0; q < upper->region_count(); ++ q) {
            const LayerRegion *ql = upper->get_region(int(q));
            if (ql == nullptr || ql->slices().surfaces.empty())
                continue;
            // Skip the region's own material (printed after its deferred infill) and same-tool
            // material (printed together, deferred infill first) - neither blocks access.
            if (ql->region().print_region_id() == infill_print_id ||
                ql->region().config().perimeter_extruder.value == infill_tool)
                continue;
            Polygons qoff = offset(ql->slices().surfaces, float(scaled<double>(clearance)));
            obstacle.insert(obstacle.end(), qoff.begin(), qoff.end());
        }
        if (obstacle.empty())
            continue;
        if (! intersection(rl->fill_expolygons(), obstacle).empty())
            blocked.insert(infill_print_id);
    }
    return blocked;
}

std::vector<IslandExtrusions> extract_island_extrusions(
    const LayerSlice &lslice,
    const Print &print,
    const Layer &layer,
    const ExtractEntityPredicate &should_pick_extrusion,
    const PathSmoothingFunction &smooth_path,
    const Point &offset,
    const unsigned extruder_id,
    std::optional<Point> &previous_position,
    // Asynchronous infill: when true this layer defers its sparse infill (printed one layer up),
    // except for regions in blocked_regions (keyed by print_region_id) whose deferred infill would
    // be inaccessible - those are printed in place with infill_first (fallback).
    const bool layer_defers,
    const std::set<int> &blocked_regions
) {
    std::vector<std::reference_wrapper<const LayerIsland>> ordered_islands = get_ordered_islands(lslice, previous_position, print.config().island_order);

    std::vector<IslandExtrusions> result;
    for (const LayerIsland &island : ordered_islands) {
        const LayerRegion &layerm = *layer.get_region(island.perimeters.region());
        // PrintObjects own the PrintRegions, thus the pointer to PrintRegion would be
        // unique to a PrintObject, they would not identify the content of PrintRegion
        // accross the whole print uniquely. Translate to a Print specific PrintRegion.
        const PrintRegion &region = print.get_print_region(layerm.region().print_region_id());

        const bool region_blocked{layer_defers && blocked_regions.count(region.print_region_id()) > 0};
        // Defer this region's sparse infill only if the layer defers and the region is accessible;
        // a blocked region keeps its sparse infill and prints it in place, infill-first (fallback a).
        const bool skip_sparse_infill{layer_defers && ! region_blocked};

        const auto should_pick_infill = [&should_pick_extrusion, skip_sparse_infill](const ExtrusionEntityCollection &eec, const PrintRegion &region) {
            if (eec.role() == ExtrusionRole::Ironing)
                return false;
            // Sparse internal infill is emitted separately at the layer below (asynchronous infill).
            if (skip_sparse_infill && eec.role().is_sparse_infill())
                return false;
            return should_pick_extrusion(eec, region);
        };

        result.push_back(IslandExtrusions{&region});
        IslandExtrusions &island_extrusions{result.back()};
        island_extrusions.infill_first = region_blocked ? true : print.config().infill_first;

        if (island_extrusions.infill_first) {
            island_extrusions.infill_ranges = extract_infill_ranges(
                print, layer, island, offset, previous_position, should_pick_infill, smooth_path, extruder_id
            );

            island_extrusions.perimeters = extract_perimeter_extrusions(print, layer, island, should_pick_extrusion, extruder_id, offset, previous_position, smooth_path);
        } else {
            island_extrusions.perimeters = extract_perimeter_extrusions(print, layer, island, should_pick_extrusion, extruder_id, offset, previous_position, smooth_path);

            island_extrusions.infill_ranges = extract_infill_ranges(
                print, layer, island, offset, previous_position, should_pick_infill, smooth_path, extruder_id
            );
        }
    }
    return result;
}

std::vector<InfillRange> extract_ironing_extrusions(
    const LayerSlice &lslice,
    const Print &print,
    const Layer &layer,
    const ExtractEntityPredicate &should_pick_extrusion,
    const PathSmoothingFunction &smooth_path,
    const Point &offset,
    const unsigned extruder_id,
    std::optional<Point> &previous_position
) {
    const auto should_pick_ironing = [&should_pick_extrusion](const auto &eec, const auto &region) {
        return should_pick_extrusion(eec, region) && eec.role() == ExtrusionRole::Ironing;
    };

    std::vector<std::reference_wrapper<const LayerIsland>> ordered_islands = get_ordered_islands(lslice, previous_position, print.config().island_order);

    std::vector<InfillRange> result;
    for (const LayerIsland &island : ordered_islands) {
        const std::vector<InfillRange> ironing_ranges{extract_infill_ranges(
            print, layer, island, offset, previous_position, should_pick_ironing, smooth_path, extruder_id
        )};
        result.insert(
            result.end(), ironing_ranges.begin(), ironing_ranges.end()
        );
    }
    return result;
}

// Asynchronous infill: collect the sparse internal infill of a whole layer (the layer below the
// one currently being printed), so it can be emitted at that layer's Z during the current pass.
std::vector<InfillRange> extract_deferred_infill_extrusions(
    const Print &print,
    const Layer &lower_layer,
    const ExtractEntityPredicate &should_pick_extrusion,
    const PathSmoothingFunction &smooth_path,
    const Point &offset,
    const unsigned extruder_id,
    std::optional<Point> &previous_position,
    // Regions (by print_region_id) whose infill is inaccessible when deferred - not pulled here,
    // they are printed in place on the lower layer instead (kept consistent with the skip logic).
    const std::set<int> &blocked_regions
) {
    const auto should_pick_sparse_infill = [&should_pick_extrusion, &blocked_regions](const ExtrusionEntityCollection &eec, const PrintRegion &region) {
        if (! eec.role().is_sparse_infill())
            return false;
        if (blocked_regions.count(region.print_region_id()) > 0)
            return false;
        return should_pick_extrusion(eec, region);
    };

    std::vector<InfillRange> result;
    for (size_t idx : lower_layer.lslice_indices_sorted_by_print_order) {
        const LayerSlice &lslice = lower_layer.lslices_ex[idx];
        for (const LayerIsland &island : get_ordered_islands(lslice, previous_position, print.config().island_order)) {
            std::vector<InfillRange> ranges{extract_infill_ranges(
                print, lower_layer, island, offset, previous_position, should_pick_sparse_infill, smooth_path, extruder_id
            )};
            for (InfillRange &range : ranges)
                result.push_back(std::move(range));
        }
    }
    return result;
}

std::vector<SliceExtrusions> get_slices_extrusions(
    const Print &print,
    const Layer &layer,
    const ExtractEntityPredicate &should_pick_extrusion,
    const PathSmoothingFunction &smooth_path,
    const Point &offset,
    const unsigned extruder_id,
    std::optional<Point> &previous_position,
    // Asynchronous infill: when true this layer defers its sparse infill (printed one layer up),
    // except for the blocked_regions (by print_region_id), which are printed in place infill-first.
    const bool layer_defers,
    const std::set<int> &blocked_regions
) {
    // Note: ironing.
    // FIXME move ironing into the loop above over LayerIslands?
    // First Ironing changes extrusion rate quickly, second single ironing may be done over
    // multiple perimeter regions. Ironing in a second phase is safer, but it may be less
    // efficient.

    std::vector<SliceExtrusions> result;

    for (size_t idx : layer.lslice_indices_sorted_by_print_order) {
        const LayerSlice &lslice = layer.lslices_ex[idx];
        std::vector<IslandExtrusions> island_extrusions{extract_island_extrusions(
            lslice, print, layer, should_pick_extrusion, smooth_path, offset, extruder_id, previous_position, layer_defers, blocked_regions
        )};
        std::vector<InfillRange> ironing_extrusions{extract_ironing_extrusions(
            lslice, print, layer, should_pick_extrusion, smooth_path, offset, extruder_id, previous_position
        )};
        if (!island_extrusions.empty() || !ironing_extrusions.empty()) {
            result.emplace_back(
                SliceExtrusions{std::move(island_extrusions), std::move(ironing_extrusions)}
            );
        }
    }
    return result;
}

// Asynchronous infill: attach infill carried over from the layer below to the first slice (a slice
// is created if this extruder prints nothing else on the current layer). It is emitted once, at
// deferred_print_z, before that slice's perimeters.
void attach_deferred_infill(std::vector<SliceExtrusions> &slices, std::vector<InfillRange> deferred, const double deferred_print_z) {
    if (deferred.empty())
        return;
    if (slices.empty())
        slices.emplace_back();
    slices.front().deferred_infill_extrusions = std::move(deferred);
    slices.front().deferred_print_z           = deferred_print_z;
}

unsigned translate_support_extruder(
    const int configured_extruder,
    const LayerTools &layer_tools,
    const ConfigOptionBools &is_soluable
) {
    if (configured_extruder <= 0) {
        // Some support will be printed with "don't care" material, preferably non-soluble.
        // Is the current extruder assigned a soluble filament?
        auto it_nonsoluble = std::find_if(layer_tools.extruders.begin(), layer_tools.extruders.end(),
            [&is_soluable](unsigned int extruder_id) { return ! is_soluable.get_at(extruder_id); });
        // There should be a non-soluble extruder available.
        assert(it_nonsoluble != layer_tools.extruders.end());
        return it_nonsoluble == layer_tools.extruders.end() ? layer_tools.extruders.front() : *it_nonsoluble;
    } else {
        return configured_extruder - 1;
    }
}

std::vector<SupportPath> get_support_extrusions(
    const unsigned int extruder_id,
    const GCode::ObjectLayerToPrint &layer_to_print,
    unsigned int support_extruder,
    unsigned int interface_extruder,
    const PathSmoothingFunction &smooth_path,
    std::optional<Point> &previous_position
) {
    if (const SupportLayer &support_layer = *layer_to_print.support_layer;
        !support_layer.support_fills.entities.empty()) {
        ExtrusionRole role = support_layer.support_fills.role();
        bool has_support = role.is_mixed() || role.is_support_base();
        bool has_interface = role.is_mixed() || role.is_support_interface();

        bool extrude_support = has_support && support_extruder == extruder_id;
        bool extrude_interface = has_interface && interface_extruder == extruder_id;

        if (extrude_support || extrude_interface) {
            ExtrusionEntitiesPtr entities_cache;
            const ExtrusionEntitiesPtr &entities = extrude_support && extrude_interface ?
                support_layer.support_fills.entities :
                entities_cache;
            if (!extrude_support || !extrude_interface) {
                auto role = extrude_support ? ExtrusionRole::SupportMaterial :
                                              ExtrusionRole::SupportMaterialInterface;
                entities_cache.reserve(support_layer.support_fills.entities.size());
                for (ExtrusionEntity *ee : support_layer.support_fills.entities)
                    if (ee->role() == role)
                        entities_cache.emplace_back(ee);
            }
            std::vector<SupportPath> paths;
            for (const ExtrusionEntityReference &entity_reference : chain_extrusion_references(entities)) {
                auto collection{dynamic_cast<const ExtrusionEntityCollection *>(&entity_reference.extrusion_entity())};
                const bool is_interface{entity_reference.extrusion_entity().role() != ExtrusionRole::SupportMaterial};
                if (collection != nullptr) {
                    for (const ExtrusionEntity * sub_entity : *collection) {
                        std::optional<InstancePoint> last_position{get_instance_point(previous_position, {0, 0})};
                        auto [path, _]{smooth_path(nullptr, nullptr, {*sub_entity, entity_reference.flipped()}, extruder_id, last_position)};
                        if (!path.empty()) {
                            paths.push_back({std::move(path), is_interface});
                        }
                        previous_position = get_gcode_point(last_position, {0, 0});
                    }
                } else {
                    std::optional<InstancePoint> last_position{get_instance_point(previous_position, {0, 0})};
                    auto [path, _]{smooth_path(nullptr, nullptr, entity_reference, extruder_id, last_position)};
                    if (!path.empty()) {
                        paths.push_back({std::move(path), is_interface});
                    }
                    previous_position = get_gcode_point(last_position, {0, 0});
                }
            }
            return paths;
        }
    }
    return {};
}

std::vector<OverridenExtrusions> get_overriden_extrusions(
    const Print &print,
    const GCode::ObjectsLayerToPrint &layers,
    const LayerTools &layer_tools,
    const std::vector<InstanceToPrint> &instances_to_print,
    const unsigned int extruder_id,
    const PathSmoothingFunction &smooth_path,
    std::optional<Point> &previous_position
) {
    std::vector<OverridenExtrusions> result;

    for (const InstanceToPrint &instance : instances_to_print) {
        if (const Layer *layer = layers[instance.object_layer_to_print_id].object_layer; layer) {
            const auto should_pick_extrusion = [&layer_tools, &instance, &extruder_id](const ExtrusionEntityCollection &entity_collection,
                                       const PrintRegion &region) {
                if (!is_overriden(entity_collection, layer_tools, instance.instance_id)) {
                    return false;
                }

                if (get_extruder_id(
                        entity_collection, layer_tools, region, instance.instance_id
                    ) != static_cast<int>(extruder_id)) {
                    return false;
                }
                return true;
            };

            const PrintObject &print_object{instance.print_object};
            const Point &offset{print_object.instances()[instance.instance_id].shift};

            // Wipe (overriding) extrusions are always printed on their own layer, so asynchronous
            // infill never skips or defers them here.
            std::vector<SliceExtrusions> slices_extrusions{get_slices_extrusions(
                print, *layer, should_pick_extrusion, smooth_path, offset, extruder_id, previous_position, /*layer_defers_infill*/ false, {}
            )};
            result.push_back({offset, std::move(slices_extrusions)});
        }
    }
    return result;
}

std::vector<NormalExtrusions> get_normal_extrusions(
    const Print &print,
    const GCode::ObjectsLayerToPrint &layers,
    const LayerTools &layer_tools,
    const ToolOrdering &tool_ordering,
    const std::vector<InstanceToPrint> &instances_to_print,
    const unsigned int extruder_id,
    const PathSmoothingFunction &smooth_path,
    std::optional<Point> &previous_position
) {
    std::vector<NormalExtrusions> result;

    // Builds the "print with this extruder, not overridden for wiping" predicate against a given
    // layer's tool ordering. Used both for the current layer and, for asynchronous infill, for the
    // layer below (whose non-overridden sparse infill is emitted during this pass).
    const auto make_should_pick = [&extruder_id](
        const LayerTools &tools, const std::size_t instance_id) {
        return [&tools, instance_id, &extruder_id](const ExtrusionEntityCollection &entity_collection, const PrintRegion &region) {
            if (is_overriden(entity_collection, tools, instance_id))
                return false;
            if (get_extruder_id(entity_collection, tools, region, instance_id) != static_cast<int>(extruder_id))
                return false;
            return true;
        };
    };

    for (std::size_t i{0}; i < instances_to_print.size(); ++i) {
        const InstanceToPrint &instance{instances_to_print[i]};
        const PrintObject &print_object = instance.print_object;
        const Point &offset = print_object.instances()[instance.instance_id].shift;

        result.emplace_back();
        result.back().instance_offset = offset;

        if (layers[instance.object_layer_to_print_id].support_layer != nullptr) {
            result.back().support_extrusions = get_support_extrusions(
                extruder_id,
                layers[instance.object_layer_to_print_id],
                translate_support_extruder(instance.print_object.config().support_material_extruder.value, layer_tools, print.config().filament_soluble),
                translate_support_extruder(instance.print_object.config().support_material_interface_extruder.value, layer_tools, print.config().filament_soluble),
                smooth_path,
                previous_position
            );
        }

        if (const Layer *layer = layers[instance.object_layer_to_print_id].object_layer; layer) {
            const auto should_pick_extrusion{make_should_pick(layer_tools, instance.instance_id)};

            // Asynchronous infill: this layer defers its own sparse infill to the layer above,
            // except for regions whose deferred infill would be inaccessible (blocked_own) - those
            // are printed in place, infill-first (fallback a). Accessibility is resolved against the
            // covering (upper) layer's tool ordering.
            const bool defers{layer_defers_infill(*layer, print)};
            const std::set<int> blocked_own{defers ? blocked_infill_regions(print, *layer, tool_ordering) : std::set<int>{}};

            result.back().slices_extrusions = get_slices_extrusions(
                print,
                *layer,
                should_pick_extrusion,
                smooth_path,
                offset,
                extruder_id,
                previous_position,
                defers,
                blocked_own
            );

            // Asynchronous infill: emit the sparse infill deferred from the layer below (if that
            // layer deferred it) at the lower layer's Z, before this layer's walls. The layer below
            // is resolved against its own tool ordering, so infill that was overridden for wiping
            // there (and thus already printed on its own layer) is correctly excluded here. Regions
            // whose deferred infill is inaccessible are skipped here - they were printed in place on
            // the lower layer's own pass (consistent with blocked_own computed there).
            if (layer->lower_layer != nullptr && layer_defers_infill(*layer->lower_layer, print)) {
                const Layer &lower_layer{*layer->lower_layer};
                const LayerTools &lower_layer_tools{tool_ordering.tools_for_layer(lower_layer.print_z)};
                const auto should_pick_deferred{make_should_pick(lower_layer_tools, instance.instance_id)};
                const std::set<int> blocked_lower{blocked_infill_regions(print, lower_layer, tool_ordering)};
                std::vector<InfillRange> deferred_infill{extract_deferred_infill_extrusions(
                    print, lower_layer, should_pick_deferred, smooth_path, offset, extruder_id, previous_position, blocked_lower
                )};
                attach_deferred_infill(result.back().slices_extrusions, std::move(deferred_infill), lower_layer.print_z);
            }
        }
    }
    return result;
}

bool is_empty(const std::vector<SliceExtrusions> &extrusions) {
    for (const SliceExtrusions &slice_extrusions : extrusions) {
        for (const IslandExtrusions &island_extrusions : slice_extrusions.common_extrusions) {
            if (!island_extrusions.perimeters.empty() || !island_extrusions.infill_ranges.empty()) {
                return false;
            }
        }
        if (!slice_extrusions.ironing_extrusions.empty()) {
            return false;
        }
        if (!slice_extrusions.deferred_infill_extrusions.empty()) {
            return false;
        }
    }
    return true;
}

bool is_empty(const ExtruderExtrusions &extruder_extrusions) {
    for (const OverridenExtrusions &overriden_extrusions : extruder_extrusions.overriden_extrusions) {
        if (!is_empty(overriden_extrusions.slices_extrusions)) {
            return false;
        }
    }
    for (const NormalExtrusions &normal_extrusions : extruder_extrusions.normal_extrusions) {
        if (!normal_extrusions.support_extrusions.empty()) {
            return false;
        }
        if (!is_empty(normal_extrusions.slices_extrusions)) {
            return false;
        }
    }
    return true;
}


std::vector<ExtruderExtrusions> get_extrusions(
    const Print &print,
    const GCode::WipeTowerIntegration *wipe_tower,
    const GCode::ObjectsLayerToPrint &layers,
    const bool is_first_layer,
    const LayerTools &layer_tools,
    const ToolOrdering &tool_ordering,
    const std::vector<InstanceToPrint> &instances_to_print,
    const std::map<unsigned int, std::pair<size_t, size_t>> &skirt_loops_per_extruder,
    unsigned current_extruder_id,
    const PathSmoothingFunction &smooth_path,
    bool get_brim,
    std::optional<Point> previous_position
) {
    unsigned toolchange_number{0};

    std::vector<ExtruderExtrusions> extrusions;
    for (const unsigned int extruder_id : layer_tools.extruders)
    {
        ExtruderExtrusions extruder_extrusions{extruder_id};

        if (layer_tools.has_wipe_tower && wipe_tower != nullptr) {
            const bool finish_wipe_tower{extruder_id == layer_tools.extruders.back()};
            if (finish_wipe_tower || is_toolchange_required(is_first_layer, layer_tools.extruders.back(), extruder_id, current_extruder_id)) {
                const bool ignore_sparse{print.config().wipe_tower_no_sparse_layers.value};
                if (const auto tool_change{wipe_tower->get_toolchange(toolchange_number, ignore_sparse)}) {
                    toolchange_number++;
                    previous_position = Point::new_scale(wipe_tower->transform_wt_pt(tool_change->end_pos));
                    current_extruder_id = tool_change->new_tool;
                    extruder_extrusions.wipe_tower_start = Point::new_scale(wipe_tower->transform_wt_pt(tool_change->start_pos));
                }
            }
        }


        if (auto loops_it = skirt_loops_per_extruder.find(extruder_id); loops_it != skirt_loops_per_extruder.end()) {
            const std::pair<size_t, size_t> loops = loops_it->second;
            for (std::size_t i = loops.first; i < loops.second; ++i) {
                bool reverse{false};
                if (auto loop = dynamic_cast<const ExtrusionLoop *>(print.skirt().entities[i])) {
                    const bool is_hole = loop->is_clockwise();
                    reverse = print.config().prefer_clockwise_movements ? !is_hole : is_hole;
                }
                const ExtrusionEntityReference entity{*print.skirt().entities[i], reverse};
                std::optional<InstancePoint> last_position{get_instance_point(previous_position, {0, 0})};
                auto [path, _]{smooth_path(nullptr, nullptr, entity, extruder_id, last_position)};
                previous_position = get_gcode_point(last_position, {0, 0});
                extruder_extrusions.skirt.emplace_back(i, std::move(path));
            }
        }

        // Extrude brim with the extruder of the 1st region.
        if (get_brim) {
            for (const ExtrusionEntity *entity : print.brim().entities) {
                bool reverse{false};
                bool is_loop{false};
                if (auto loop = dynamic_cast<const ExtrusionLoop *>(entity)) {
                    const bool is_hole = loop->is_clockwise();
                    is_loop = true;
                    reverse = print.config().prefer_clockwise_movements ? !is_hole : is_hole;
                }
                const ExtrusionEntityReference entity_reference{*entity, reverse};

                std::optional<InstancePoint> last_position{get_instance_point(previous_position, {0, 0})};
                auto [path, _]{smooth_path(nullptr, nullptr, entity_reference, extruder_id, last_position)};
                previous_position = get_gcode_point(last_position, {0, 0});
                extruder_extrusions.brim.push_back({std::move(path), is_loop});
            }
            get_brim = false;
        }

        using GCode::ExtrusionOrder::get_overriden_extrusions;
        bool is_anything_overridden = layer_tools.wiping_extrusions().is_anything_overridden();
        if (is_anything_overridden) {
            extruder_extrusions.overriden_extrusions = get_overriden_extrusions(
                print, layers, layer_tools, instances_to_print, extruder_id, smooth_path,
                previous_position
            );
        }

        using GCode::ExtrusionOrder::get_normal_extrusions;
        extruder_extrusions.normal_extrusions = get_normal_extrusions(
            print, layers, layer_tools, tool_ordering, instances_to_print, extruder_id, smooth_path,
            previous_position
        );

        extrusions.push_back(std::move(extruder_extrusions));
    }
    return extrusions;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const SmoothPath &path) {
    for (const SmoothPathElement & element : path) {
        if (!element.path.empty()) {
            return element.path.front();
        }
    }
    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const std::vector<SmoothPath> &smooth_paths) {
    for (const SmoothPath &path : smooth_paths) {
        if (auto result = get_first_point(path)) {
            return result;
        }
    }
    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const std::vector<InfillRange> &infill_ranges) {
    for (const InfillRange &infill_range : infill_ranges) {
        if (auto result = get_first_point(infill_range.items)) {
            return result;
        }
    }
    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const std::vector<Perimeter> &perimeters) {
    for (const Perimeter &perimeter : perimeters) {
        if (auto result = get_first_point(perimeter.smooth_path)) {
            return result;
        }
    }
    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const std::vector<IslandExtrusions> &extrusions) {
    for (const IslandExtrusions &island : extrusions) {
        if (island.infill_first) {
            if (auto result = get_first_point(island.infill_ranges)) {
                return result;
            }
            if (auto result = get_first_point(island.perimeters)) {
                return result;
            }
        } else {
            if (auto result = get_first_point(island.perimeters)) {
                return result;
            }
            if (auto result = get_first_point(island.infill_ranges)) {
                return result;
            }
        }
    }
    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const std::vector<SliceExtrusions> &extrusions) {
    for (const SliceExtrusions &slice : extrusions) {
        // Deferred infill is emitted before the common extrusions, so it is the first point.
        if (auto result = get_first_point(slice.deferred_infill_extrusions)) {
            return result;
        }
        if (auto result = get_first_point(slice.common_extrusions)) {
            return result;
        }
    }
    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const ExtruderExtrusions &extrusions) {
    for (const auto&[_, path] : extrusions.skirt) {
        if (auto result = get_first_point(path)) {
            return result;
        };
    }
    for (const BrimPath &brim_path : extrusions.brim) {
        if (auto result = get_first_point(brim_path.path)) {
            return result;
        };
    }
    for (const OverridenExtrusions &overriden_extrusions : extrusions.overriden_extrusions) {
        if (auto result = get_first_point(overriden_extrusions.slices_extrusions)) {
            result->point += overriden_extrusions.instance_offset;
            return result;
        }
    }

    for (const NormalExtrusions &normal_extrusions : extrusions.normal_extrusions) {
        for (const SupportPath &support_path : normal_extrusions.support_extrusions) {
            if (auto result = get_first_point(support_path.path)) {
                result->point += normal_extrusions.instance_offset;
                return result;
            }
        }
        if (auto result = get_first_point(normal_extrusions.slices_extrusions)) {
            result->point += normal_extrusions.instance_offset;
            return result;
        }
    }

    return std::nullopt;
}

std::optional<Geometry::ArcWelder::Segment> get_first_point(const std::vector<ExtruderExtrusions> &extrusions) {
    if (extrusions.empty()) {
        return std::nullopt;
    }

    if (extrusions.front().wipe_tower_start) {
        return {{*(extrusions.front().wipe_tower_start)}};
    }

    for (const ExtruderExtrusions &extruder_extrusions : extrusions) {
        if (auto result = get_first_point(extruder_extrusions)) {
            return result;
        }
    }

    return std::nullopt;
}

const PrintInstance * get_first_instance(
    const std::vector<ExtruderExtrusions> &extrusions,
    const std::vector<InstanceToPrint> &instances_to_print
) {
    if (instances_to_print.empty()) {
        return nullptr;
    }

    for (const ExtruderExtrusions &extruder_extrusions : extrusions) {
        if (!extruder_extrusions.overriden_extrusions.empty()) {
            for (std::size_t i{0}; i < instances_to_print.size(); ++i) {
                const OverridenExtrusions &overriden_extrusions{extruder_extrusions.overriden_extrusions[i]};
                if (!is_empty(overriden_extrusions.slices_extrusions)) {
                    const InstanceToPrint &instance{instances_to_print[i]};
                    return &instance.print_object.instances()[instance.instance_id];
                }
            }
        }
        for (std::size_t i{0}; i < instances_to_print.size(); ++i) {
            const InstanceToPrint &instance{instances_to_print[i]};
            const std::vector<SupportPath> &support_extrusions{extruder_extrusions.normal_extrusions[i].support_extrusions};
            const std::vector<SliceExtrusions> &slices_extrusions{extruder_extrusions.normal_extrusions[i].slices_extrusions};

            if (!support_extrusions.empty() || !is_empty(slices_extrusions)) {
                return &instance.print_object.instances()[instance.instance_id];
            }
        }
    }
    const InstanceToPrint &instance{instances_to_print.front()};
    return &instance.print_object.instances()[instance.instance_id];
}

}
