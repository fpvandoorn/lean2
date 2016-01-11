/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/static_matrix.h"
#include "util/lp/lp_core_solver_base.h"
#include <string>
#include <limits>
#include <set>
#include <algorithm>
#include <vector>

namespace lean {
template <typename T, typename X>
class lp_dual_core_solver:public lp_core_solver_base<T, X> {
public:
    std::vector<bool> & m_can_enter_basis;
    int m_r; // the row of the leaving column
    int m_p; // leaving column; that is m_p = m_basis[m_r]
    T m_delta; // the offset of the leaving basis variable
    int m_sign_of_alpha_r; // see page 27
    T m_theta_D;
    T m_theta_P;
    int m_q;
    // todo : replace by a vector later
    std::set<unsigned> m_breakpoint_set; // it is F in "Progress in the dual simplex method ..."
    std::set<unsigned> m_flipped_boxed;
    std::set<unsigned> m_tight_set; // it is the set of all breakpoints that become tight when m_q becomes tight
    std::vector<T> m_a_wave;
    std::vector<T> m_betas; // m_betas[i] is approximately a square of the norm of the i-th row of the reverse of B
    T m_harris_tolerance;

    lp_dual_core_solver(static_matrix<T, X> & A,
                        std::vector<bool> & can_enter_basis,
                        std::vector<X> & b, // the right side std::vector
                        std::vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                        std::vector<unsigned> & basis,
                        std::vector<T> & costs,
                        std::vector<column_type> & column_type_array,
                        std::vector<X> & low_bound_values,
                        std::vector<X> & upper_bound_values,
                        lp_settings & settings,
                        std::unordered_map<unsigned, std::string> const & column_names):
        lp_core_solver_base<T, X>(A,
                               b,
                               basis,
                               x,
                               costs,
                               settings,
                               column_names,
                               column_type_array,
                               low_bound_values,
                               upper_bound_values),
        m_can_enter_basis(can_enter_basis),
        m_a_wave(this->m_m),
        m_betas(this->m_m) {
        m_harris_tolerance = numeric_traits<T>::precise()? numeric_traits<T>::zero() : T(this->m_settings.harris_feasibility_tolerance);
        this->solve_yB(this->m_y);
        init_basic_part_of_basis_heading(this->m_basis, this->m_m, this->m_basis_heading);
        fill_non_basis_with_only_able_to_enter_columns();
    }

    void init_a_wave_by_zeros() {
        unsigned j = this->m_m;
        while (j--) {
            m_a_wave[j] = numeric_traits<T>::zero();
        }
    }

    void fill_non_basis_with_only_able_to_enter_columns() {
        auto & nb = this->m_factorization->m_non_basic_columns;
        nb.clear();
        unsigned j = this->m_n;
        while (j--) {
            if (this->m_basis_heading[j] >= 0 || !m_can_enter_basis[j]) continue;
            nb.push_back(j);
            this->m_basis_heading[j] = - nb.size();
        }
    }

    void print_nb() {
        std::cout << "this is nb " << std::endl;
        for (auto l : this->m_factorization->m_non_basic_columns) {
            std::cout << l << " ";
        }
        std::cout << std::endl;
    }

    void restore_non_basis() {
        auto & nb = this->m_factorization->m_non_basic_columns;
        nb.clear();
        unsigned j = this->m_n;
        while (j--) {
            if (this->m_basis_heading[j] >= 0 ) continue;
            if (m_can_enter_basis[j]) {
                lean_assert(std::find(nb.begin(), nb.end(), j) == nb.end());
                nb.push_back(j);
                this->m_basis_heading[j] = - nb.size();
            }
        }
    }

    bool update_basis(int entering, int leaving) {
            // the second argument is the element of the entering column from the pivot row - its value should be equal to the low diagonal element of the bump after all pivoting is done
        if (!(this->m_refactor_counter++ >= 200)) {
            this->m_factorization->replace_column(leaving, this->m_ed[this->m_factorization->basis_heading(leaving)], this->m_w);
            if (this->m_factorization->get_status() != LU_status::OK) {
                std::cout << "failed on replace_column( " << leaving << ", " <<  this->m_ed[this->m_factorization->basis_heading(leaving)] << ") total_iterations = " << this->m_total_iterations << std::endl;
                init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_basis_heading, this->m_settings, this->m_non_basic_columns);
                this->m_iters_with_no_cost_growing++;
                this->m_status = UNSTABLE;
                return false;
            }
            this->m_factorization->change_basis(entering, leaving);
        } else { // need to refactor
            this->m_factorization->change_basis(entering, leaving);
            init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_basis_heading, this->m_settings, this->m_non_basic_columns);
            if (this->m_factorization->get_status() != LU_status::OK) {
                std::cout << "failing refactor for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << this->m_total_iterations << std::endl;
                this->m_iters_with_no_cost_growing++;
                return false;
            }
        }
        return true;
    }

    void recalculate_xB_and_d() {
        this->solve_Ax_eq_b();
        recalculate_d();
    }

    void recalculate_d() {
       this->solve_yB(this->m_y);
       this->fill_reduced_costs_from_m_y_by_rows();
    }

    std::vector<unsigned> & non_basis() { return this->m_factorization->m_non_basic_columns; }

    void init_betas() {
        // todo : look at page 194 of Progress in the dual simplex algorithm for solving large scale LP problems : techniques for a fast and stable implementation
        // the current implementation is not good enough: todo
        unsigned i = this->m_m;
        while (i--) {
            m_betas[i] = 1;
        }
    }

    void adjust_xb_for_changed_xn_and_init_betas() {
        this->solve_Ax_eq_b();
        init_betas();
    }

    void start_with_initial_basis_and_make_it_dual_feasible() {
        this->set_non_basic_x_to_correct_bounds(); // It is not an efficient version, see 3.29,
        // however this version does not require that m_x is the solution of Ax = 0 beforehand
        adjust_xb_for_changed_xn_and_init_betas();
    }

    bool done() {
        if (this->m_status == OPTIMAL) {
            return true;
        }
        if (this->m_total_iterations > this->m_settings.max_total_number_of_iterations) { // debug !!!!
            this->m_status = ITERATIONS_EXHAUSTED;
            return true;
        }
        return false; // todo, need to be more cases
    }

    T get_edge_steepness_for_low_bound(unsigned p) {
        lean_assert(this->m_basis_heading[p] >= 0 && this->m_basis_heading[p] < this->m_m);
        T del = this->m_x[p] - this->m_low_bound_values[p];
        del *= del;
        return del / this->m_betas[this->m_basis_heading[p]];
    }

    T get_edge_steepness_for_upper_bound(unsigned p) {
        lean_assert(this->m_basis_heading[p] >= 0 && this->m_basis_heading[p] < this->m_m);
        T del = this->m_x[p] - this->m_upper_bound_values[p];
        del *= del;
        return del / this->m_betas[this->m_basis_heading[p]];
    }

    // void print_x_and_low_bound(unsigned p) {
    //     std::cout << "x l[" << p << "] = " << this->m_x[p] << " " << this->m_low_bound_values[p] << std::endl;
    // }
    // void print_x_and_upper_bound(unsigned p) {
    //     std::cout << "x u[" << p << "] = " << this->m_x[p] << " " << this->m_upper_bound_values[p] << std::endl;
    // }

    // returns the
    T pricing_for_row(unsigned i) {
        unsigned p = this->m_basis[i];
        switch (this->m_column_type[p]) {
        case fixed:
        case boxed:
            if (this->x_below_low_bound(p)) {
                T del =  get_edge_steepness_for_low_bound(p);
                // std::cout << "case boxed low_bound in pricing" << std::endl;
                // print_x_and_low_bound(p);
                return del;
            }
            if (this->x_above_upper_bound(p)) {
                T del =  get_edge_steepness_for_upper_bound(p);
                // std::cout << "case boxed at upper_bound in pricing" << std::endl;
                // print_x_and_upper_bound(p);
                return del;
            }
            return numeric_traits<T>::zero();
        case low_bound:
            if (this->x_below_low_bound(p)) {
                T del =  get_edge_steepness_for_low_bound(p);
                // std::cout << "case low_bound in pricing" << std::endl;
                // print_x_and_low_bound(p);
                return del;
            }
            return numeric_traits<T>::zero();
            break;
        case upper_bound:
            if (this->x_above_upper_bound(p)) {
                T del =  get_edge_steepness_for_upper_bound(p);
                // std::cout << "case upper_bound in pricing" << std::endl;
                // print_x_and_upper_bound(p);
                return del;
            }
            return numeric_traits<T>::zero();
            break;
        case free_column:
            lean_assert(numeric_traits<T>::is_zero(this->m_d[p]));
            return numeric_traits<T>::zero();
        default:
            lean_unreachable();
        }
     }

    void pricing_loop(unsigned number_of_rows_to_try, unsigned offset_in_rows) {
        m_r = -1;
        T steepest_edge_max = numeric_traits<T>::zero();
        unsigned initial_offset_in_rows = offset_in_rows;
        unsigned i = offset_in_rows;
        unsigned rows_left = number_of_rows_to_try;
        do  {
        loop_start:
            T se = pricing_for_row(i);
            if (se > steepest_edge_max) {
                steepest_edge_max = se;
                m_r = i;
            }
            if (++i == this->m_m) {
                i = 0;
            }
            if (rows_left > 0) {
                rows_left--;
            }
        }  while (rows_left || (steepest_edge_max < T(1e-5) && i != initial_offset_in_rows));
        if (m_r == -1) {
            if (this->m_status != UNSTABLE) {
                this->m_status = OPTIMAL;
            }
        } else {
            m_p = this->m_basis[m_r];
            m_delta = get_delta();
            if (advance_on_known_p()){
                return;
            }
            if (this->m_status == FLOATING_POINT_ERROR) {
                return;
            }
            this->m_status = UNSTABLE;
            if (i == initial_offset_in_rows) {
                return; // made a full loop
            }
            m_p = m_r = -1;
            steepest_edge_max = numeric_traits<T>::zero();
            rows_left = number_of_rows_to_try;
            goto loop_start;
            // if (this->m_total_iterations % 80 == 0) {
            //     std::cout << "m_delta = " << m_delta << std::endl;
            // }
        }
    }

    bool advance_on_known_p() {
        if (done()) {
            return true;
        }
        this->calculate_pivot_row_of_B_1(m_r);
        this->calculate_pivot_row_when_pivot_row_of_B1_is_ready();
        if (!ratio_test()) {
            return true;
        }
        calculate_beta_r_precisely();
        FTran();
        DSE_FTran();
        return basis_change_and_update();
    }

    int define_sign_of_alpha_r() {
        switch (this->m_column_type[m_p]) {
        case boxed:
        case fixed:
            if (this->x_below_low_bound(m_p)) {
                return -1;
            }
            if (this->x_above_upper_bound(m_p)) {
                return 1;
            }
            lean_unreachable();
        case low_bound:
            if (this->x_below_low_bound(m_p)) {
                return -1;
            }
            lean_unreachable();
        case upper_bound:
            if (this->x_above_upper_bound(m_p)) {
                return 1;
            }
            lean_unreachable();
        default:
            lean_unreachable();
        }
    }

    bool can_be_breakpoint(unsigned j) {
        if (this->pivot_row_element_is_too_small_for_ratio_test(j)) return false;
        switch (this->m_column_type[j]) {
        case low_bound:
            lean_assert(this->m_settings.abs_val_is_smaller_than_harris_tolerance(this->m_x[j] - this->m_low_bound_values[j]));
            return m_sign_of_alpha_r * this->m_pivot_row[j]  > 0;
        case upper_bound:
            lean_assert(this->m_settings.abs_val_is_smaller_than_harris_tolerance(this->m_x[j] - this->m_upper_bound_values[j]));
            return m_sign_of_alpha_r * this->m_pivot_row[j] < 0;
        case boxed:
            {
                bool low_bound = this->x_is_at_low_bound(j);
                bool grawing = m_sign_of_alpha_r * this->m_pivot_row[j] > 0;
                return low_bound == grawing;
            }
        case fixed: // is always dual feasible so we ingore it
            return false;
        case free_column:
                return true;
        default:
            return false;
        }
    }

    void fill_breakpoint_set() {
        m_breakpoint_set.clear();
        for (unsigned j : non_basis()) {
            if (can_be_breakpoint(j)) {
                m_breakpoint_set.insert(j);
            }
        }
    }

    void FTran() {
        this->solve_Bd(m_q);
    }

    // this calculation is needed for the steepest edge update,
    // it hijackes m_pivot_row_of_B_1 for this purpose since we will need it anymore to the end of the cycle
    void DSE_FTran() { // todo, see algorithm 7 from page 35
        this->m_factorization->solve_By(this->m_pivot_row_of_B_1);
    }

    T get_delta() {
        switch (this->m_column_type[m_p]) {
        case boxed:
            if (this->x_below_low_bound(m_p)) {
                return this->m_x[m_p] - this->m_low_bound_values[m_p];
            }
            if (this->x_above_upper_bound(m_p)) {
                return this->m_x[m_p] - this->m_upper_bound_values[m_p];;
            }
            lean_unreachable();
        case low_bound:
            if (this->x_below_low_bound(m_p)) {
                return this->m_x[m_p] - this->m_low_bound_values[m_p];
            }
            lean_unreachable();
        case upper_bound:
            if (this->x_above_upper_bound(m_p)) {
                return get_edge_steepness_for_upper_bound(m_p);
            }
            lean_unreachable();
        case fixed:
            return this->m_x[m_p] - this->m_upper_bound_values[m_p];;
        default:
            lean_unreachable();
        }
    }

    void restore_d() {
        std::cout << "restore_d" << std::endl;
        this->m_d[m_p] = numeric_traits<T>::zero();
        for (auto j : non_basis()) {
            this->m_d[j] += m_theta_D * this->m_pivot_row[j];
        }
    }

    bool d_is_correct() {
        this->solve_yB(this->m_y);
        for  (auto j : non_basis()) {
            T d = this->m_costs[j] -  this->m_A.dot_product_with_column(this->m_y, j);
            if (numeric_traits<T>::get_double(abs(d - this->m_d[j])) >= 0.001) {
                std::cout << "m_total_iterations = " << this->m_total_iterations << std::endl;
                std::cout << "d[" << j << "] = " << this->m_d[j] << " but should be " << d << std::endl;
                return false;
            }
        }
        return true;
    }

    void xb_minus_delta_p_pivot_column() {
        unsigned i = this->m_m;
        while (i--) {
            this->m_x[this->m_basis[i]] -= m_theta_P * this->m_ed[i];
        }
    }

    void update_betas() { // page 194 of Progress ... todo - once in a while betas have to be reinitialized
        T one_over_arq = numeric_traits<T>::one() / this->m_pivot_row[m_q];
        T beta_r = this->m_betas[m_r] = std::max(T(0.0001), (m_betas[m_r] * one_over_arq) *  one_over_arq);
        T k = -2 * one_over_arq;
        unsigned i = this->m_m;
        while (i--) {
            if (i == m_r) continue;
            T a = this->m_ed[i];
            m_betas[i] += a * (a * beta_r + k * this->m_pivot_row_of_B_1[i]);
            if (m_betas[i] < T(0.0001))
                m_betas[i] = T(0.0001);
        }
    }

    void apply_flips() {
        for (unsigned j : m_flipped_boxed) {
            lean_assert(this->x_is_at_bound(j));
            if (this->x_is_at_low_bound(j)) {
                this->m_x[j] = this->m_upper_bound_values[j];
            } else {
                this->m_x[j] = this->m_low_bound_values[j];
            }
        }
    }

    void snap_xN_column_to_bounds(unsigned j) {
        switch (this->m_column_type[j]) {
        case fixed:
            this->m_x[j] = this->m_low_bound_values[j];
            break;
        case boxed:
            if (this->x_is_at_low_bound(j)) {
                this->m_x[j] = this->m_low_bound_values[j];
            } else {
                this->m_x[j] = this->m_upper_bound_values[j];
            }
            break;
        case low_bound:
            this->m_x[j] = this->m_low_bound_values[j];
            break;
        case upper_bound:
            this->m_x[j] = this->m_upper_bound_values[j];
            break;
        case free_column:
            break;
        default:
            lean_unreachable();
        }
    }

    void snap_xN_to_bounds() {
        for (auto j : this->non_basis()) {
            snap_xN_column_to_bounds(j);
        }
    }

    void init_beta_precisely(unsigned i) {
        std::vector<T> vec(this->m_m, numeric_traits<T>::zero());
        vec[i] = numeric_traits<T>::one();
        this->m_factorization->solve_yB(vec);
        T beta = numeric_traits<T>::zero();
        for (T & v : vec) {
            beta += v * v;
        }
        this->m_betas[i] =beta;
    }

    void init_betas_precisely() {
        std::cout << "init beta precisely..." << std::endl;
        unsigned i = this->m_m;
        while (i--) {
            init_beta_precisely(i);
        }
        std::cout << "done" << std::endl;
    }

    // step 7 of the algorithm from Progress
    bool basis_change_and_update() {
        update_betas();
        update_d_and_xB();
        m_theta_P = m_delta / this->m_ed[m_r];
        xb_minus_delta_p_pivot_column();
        apply_flips();
        this->m_x[m_q] += m_theta_P;
        if (!update_basis(m_q, m_p) || this->A_mult_x_is_off() || !problem_is_dual_feasible()) {
            revert_to_previous_basis();
            this->m_iters_with_no_cost_growing++;
            return false;
        }
        lean_assert(d_is_correct());
        return true;
    }

    void revert_to_previous_basis() {
        std::cout << "recovering basis p = " << m_p << " q = " << m_q << std::endl;
        this->m_factorization->change_basis(m_p, m_q);
        init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_basis_heading, this->m_settings, this->m_non_basic_columns);
        if (this->m_factorization->get_status() != LU_status::OK) {
            this->m_status = FLOATING_POINT_ERROR;
            return;
        }
        this->m_x[m_q] -= m_theta_P;
        snap_xN_to_bounds();
        recalculate_xB_and_d();
        if (this->A_mult_x_is_off()) {
            this->m_status = FLOATING_POINT_ERROR;
            return;
        }
        init_betas_precisely();
    }


    bool problem_is_dual_feasible() {
        for (unsigned j : non_basis()){
            if (!this->column_is_dual_feasible(j)) {
                std::cout << "column " << j << " is not dual feasible" << std::endl;
                std::cout << "m_d[" << j << "] = " << this->m_d[j] << std::endl;
                std::cout << "x[" << j << "] = " << this->m_x[j] << std::endl;
                std::cout << "type = " << column_type_to_string(this->m_column_type[j]) << std::endl;
                std::cout << "bounds = " << this->m_low_bound_values[j] << "," << this->m_upper_bound_values[j] << std::endl;
                std::cout << "m_total_iterations = " << this->m_total_iterations << std::endl;
                return false;
            }
        }
        return true;
    }

    unsigned get_number_of_rows_to_try_for_leaving() {
        unsigned s = this->m_m;
        if (this->m_m > 300) {
            s = (unsigned)(s / this->m_settings.percent_of_entering_to_check * 100);
        }
        return lrand48() % s + 1;
    }

    void update_a_wave(const T & del, unsigned j) {
        this->m_A.add_column_to_vector(del, j, & m_a_wave[0]);
    }

    bool delta_keeps_the_sign(int initial_delta_sign, const T & delta) {
        if (numeric_traits<T>::precise())
            return ((delta > numeric_traits<T>::zero()) && (initial_delta_sign == 1)) ||
                ((delta < numeric_traits<T>::zero()) && (initial_delta_sign == -1));

        double del = numeric_traits<T>::get_double(delta);
        return ( (del > this->m_settings.zero_tolerance) && (initial_delta_sign == 1)) ||
                ((del < - this->m_settings.zero_tolerance) && (initial_delta_sign == -1));
    }

    void set_status_to_tentative_dual_unbounded_or_dual_unbounded() {
        std::cout << "cost = " << this->get_cost() << std::endl;
        if (this->m_status == TENTATIVE_DUAL_UNBOUNDED) {
            std::cout << "setting status to DUAL_UNBOUNDED" << std::endl;
            this->m_status = DUAL_UNBOUNDED;
        } else {
            std::cout << "setting to TENTATIVE_DUAL_UNBOUNDED" << std::endl;
            this->m_status = TENTATIVE_DUAL_UNBOUNDED;
        }
    }

    // it is positive if going from low bound to upper bound and negative if going from upper bound to low bound
    T signed_span_of_boxed(unsigned j) {
        return this->x_is_at_low_bound(j)? this->bound_span(j): - this->bound_span(j);
    }

    void add_tight_breakpoints_and_q_to_flipped_set() {
        m_flipped_boxed.insert(m_q);
        for (auto j : m_tight_set) {
            m_flipped_boxed.insert(j);
        }
    }

    T delta_lost_on_flips_of_tight_breakpoints() {
        T ret = abs(this->bound_span(m_q) * this->m_pivot_row[m_q]);
        for (auto j : m_tight_set) {
            ret += abs(this->bound_span(j) * this->m_pivot_row[j]);
        }
        return ret;
    }

    bool tight_breakpoinst_are_all_boxed() {
        if (this->m_column_type[m_q] != boxed) return false;
        for (auto j : m_tight_set) {
            if (this->m_column_type[j] != boxed) return false;
        }
        return true;
    }

    T calculate_harris_delta_on_breakpoint_set() {
        bool first_time = true;
        T ret = zero_of_type<T>();
        lean_assert(m_breakpoint_set.size() > 0);
        for (auto j : m_breakpoint_set) {
            T t;
            if (this->x_is_at_low_bound(j)) {
                t = abs((std::max(this->m_d[j], numeric_traits<T>::zero()) + m_harris_tolerance) / this->m_pivot_row[j]);
            } else {
                t = abs((std::min(this->m_d[j], numeric_traits<T>::zero()) - m_harris_tolerance) / this->m_pivot_row[j]);
            }
            if (first_time) {
                ret = t;
                first_time = false;
            } else if (t < ret) {
                ret = t;
            }
        }
        return ret;
    }

    void fill_tight_set_on_harris_delta(const T & harris_delta ){
        m_tight_set.clear();
        for (auto j : m_breakpoint_set) {
            if (this->x_is_at_low_bound(j)) {
                if (abs(std::max(this->m_d[j], numeric_traits<T>::zero()) / this->m_pivot_row[j]) <= harris_delta){
                    m_tight_set.insert(j);
                }
            } else {
                if (abs(std::min(this->m_d[j], numeric_traits<T>::zero() ) / this->m_pivot_row[j]) <= harris_delta){
                    m_tight_set.insert(j);
                }
            }
        }
    }

    void find_q_on_tight_set() {
        m_q = -1;
        T max_pivot;
        for (auto j : m_tight_set) {
            T r = abs(this->m_pivot_row[j]);
            if (m_q != -1) {
                if (r > max_pivot) {
                    max_pivot = r;
                    m_q = j;
                }
            } else {
                max_pivot = r;
                m_q = j;
            }
        }
        m_tight_set.erase(m_q);
    }

    void find_q_and_tight_set() {
       T harris_del = calculate_harris_delta_on_breakpoint_set();
        fill_tight_set_on_harris_delta(harris_del);
        find_q_on_tight_set();
        lean_assert(m_q != -1);
    }

    void erase_tight_breakpoints_and_q_from_breakpoint_set() {
            m_breakpoint_set.erase(m_q);
            for (auto j : m_tight_set) {
                m_breakpoint_set.erase(j);
            }
    }

    bool ratio_test() {
        m_sign_of_alpha_r = define_sign_of_alpha_r();
        fill_breakpoint_set();
        m_flipped_boxed.clear();
        int initial_delta_sign = m_delta >= numeric_traits<T>::zero()? 1: -1;
        do {
            if (m_breakpoint_set.size() == 0) {
                set_status_to_tentative_dual_unbounded_or_dual_unbounded();
                return false;
            }
            this->m_status = FEASIBLE;
            find_q_and_tight_set();
            if (!tight_breakpoinst_are_all_boxed())  break;
            T del = m_delta - delta_lost_on_flips_of_tight_breakpoints() * initial_delta_sign;
            if (!delta_keeps_the_sign(initial_delta_sign, del)) break;
            if (m_tight_set.size() + 1 == m_breakpoint_set.size()) {
                break; // deciding not to flip since we might get stuck without finding m_q, the column entering the basis
            }
            // we can flip m_q together with the tight set and look for another breakpoint candidate for m_q and another tight set
            add_tight_breakpoints_and_q_to_flipped_set();
            m_delta = del;
            erase_tight_breakpoints_and_q_from_breakpoint_set();
        } while (true);
        m_theta_D = this->m_d[m_q] / this->m_pivot_row[m_q];
        return true;
    }

    void process_flipped() {
       init_a_wave_by_zeros();
       for (auto j : m_flipped_boxed) {
           update_a_wave(signed_span_of_boxed(j), j);
       }
    }
    void update_d_and_xB() {
        for (auto j : non_basis()) {
            this->m_d[j] -= m_theta_D * this->m_pivot_row[j];
        }
        this->m_d[m_p] = - m_theta_D;
        if (m_flipped_boxed.size() > 0) {
            process_flipped();
            update_xb_after_bound_flips();
        }
    }

    void calculate_beta_r_precisely() {
        T t = numeric_traits<T>::zero();
        unsigned i = this->m_m;
        while (i--) {
            T b = this->m_pivot_row_of_B_1[i];
            t += b * b;
        }
        m_betas[m_r] = t;
    }
    // see "Progress in the dual simplex method for large scale LP problems: practical dual phase 1 algorithms"

    void update_xb_after_bound_flips() {
        this->m_factorization->solve_By(m_a_wave);
        unsigned i = this->m_m;
        while (i--) {
            this->m_x[this->m_basis[i]] -= m_a_wave[i];
        }
     }

    void one_iteration() {
        unsigned number_of_rows_to_try = get_number_of_rows_to_try_for_leaving();
        unsigned offset_in_rows = lrand48() % this->m_m;
        if (this->m_status == TENTATIVE_DUAL_UNBOUNDED) {
            number_of_rows_to_try = this->m_m;
        } else {
            this->m_status = FEASIBLE;
        }
        pricing_loop(number_of_rows_to_try, offset_in_rows);
        lean_assert(problem_is_dual_feasible());
    }

    void solve() { // see the page 35
        lean_assert(d_is_correct());
        lean_assert(problem_is_dual_feasible());
        this->m_start_time = get_millisecond_count();
        lean_assert(this->basis_heading_is_correct());
        this->m_total_iterations = 0;
        this->m_iters_with_no_cost_growing = 0;
        do {
            if (this->print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(std::string(), this->m_total_iterations)){
                this->m_status = lp_status::TIME_EXHAUSTED;
                return;
            }
            one_iteration();
            this->m_total_iterations++;
        } while (this->m_status != FLOATING_POINT_ERROR && this->m_status != DUAL_UNBOUNDED && this->m_status != OPTIMAL &&
                 this->m_iters_with_no_cost_growing <= this->m_settings.max_number_of_iterations_with_no_improvements
                 && this->m_total_iterations <= this->m_settings.max_total_number_of_iterations);
    }

    bool low_bounds_are_set() const { return true; }
};
}