// Produce real GOTO fixtures and independent constant-expression answers from CBMC.
#include <goto-programs/goto_model.h>
#include <goto-programs/write_goto_binary.h>
#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/cmdline.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/validate.h>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

int main(int argc, char **argv) {
  try {
    if (argc != 2) throw std::runtime_error("expected output GOTO filename");
    cmdlinet defaults;
    config.set(defaults);
    goto_modelt model;
    namespacet ns(model.symbol_table);
    source_locationt loc;
    loc.set_file("tests/ir.cpp");
    loc.set_line(1);
    loc.set_property_id("ir.fixture");
    loc.set_comment("IR oracle; escaped \"quote\", backslash \\ and newline\nnext line");
    auto add = [&](const std::string &name, const exprt &expr, bool oracle = true) {
      symbolt sym;
      sym.name = name; sym.base_name = name; sym.mode = ID_C;
      sym.type = code_typet({}, expr.type());
      model.symbol_table.add(sym);
      auto &body = model.goto_functions.function_map[name].body;
      body.add(goto_programt::make_set_return_value(expr, loc));
      body.add(goto_programt::make_end_function(loc));
      if (oracle) {
        auto result = simplify_expr(expr, ns);
        if (result.id() != ID_constant) throw std::runtime_error("oracle did not simplify: " + name);
        if (result.type().id() == ID_bool)
          std::cout << name << '\t' << (result == true ? "true" : "false") << '\n';
        else {
          mp_integer value;
          if (to_integer(to_constant_expr(result), value)) throw std::runtime_error("invalid oracle value");
          std::cout << name << '\t' << value << '\n';
        }
      }
    };
    for (unsigned w : {8u, 32u, 64u, 128u}) {
      const unsignedbv_typet u(w);
      const signedbv_typet s(w);
      for (unsigned n : {0u, 1u, w - 1, w, w + 1, 255u}) {
        const auto suffix = std::to_string(w) + "_" + std::to_string(n);
        const auto all = from_integer(-1, u), high = from_integer(mp_integer(1) << (w - 1), s);
        add("left_" + suffix, shl_exprt(all, n));
        add("right_" + suffix, lshr_exprt(all, n));
        add("signed_" + suffix, ashr_exprt(high, n));
      }
      auto a = from_integer(-7, s), b = from_integer(2, s);
      add("div_" + std::to_string(w), div_exprt(a, b));
      add("rem_" + std::to_string(w), mod_exprt(a, b));
      add("lt_" + std::to_string(w), binary_relation_exprt(a, ID_lt, b));
      for (bool sign : {false, true}) {
        const typet &t = sign ? static_cast<const typet &>(s) : static_cast<const typet &>(u);
        const mp_integer high = mp_integer(1) << (w - 1);
        const std::vector<std::pair<mp_integer, mp_integer>> pairs = {
          {-1, 1}, {high - 1, 1}, {high, 1}, {high, -1}, {0, 1}, {2, high - 1}};
        for (std::size_t i = 0; i < pairs.size(); ++i) {
          auto x = from_integer(pairs[i].first, t), y = from_integer(pairs[i].second, t);
          const auto suffix = std::string(sign ? "s" : "u") + std::to_string(w) + "_" +
            std::to_string(i);
          add("overflow_add_" + suffix, plus_overflow_exprt(x, y));
          add("overflow_sub_" + suffix, minus_overflow_exprt(x, y));
          add("overflow_mul_" + suffix, mult_overflow_exprt(x, y));
        }
      }
    }
    const unsignedbv_typet u(8);
    const array_typet array_type(u, from_integer(3, unsignedbv_typet(32)));
    const array_exprt array({from_integer(7, u), from_integer(19, u), from_integer(31, u)}, array_type);
    for (unsigned i = 0; i < 3; ++i) {
      const auto index = from_integer(i, signedbv_typet(32));
      add("array_literal_" + std::to_string(i), index_exprt(array, index, u));
      add("array_update_" + std::to_string(i), index_exprt(
        with_exprt(array, index, from_integer(41, u)), index, u));
    }
    add("array_negative_update", index_exprt(
      with_exprt(array, from_integer(-1, signedbv_typet(32)), from_integer(41, u)),
      from_integer(0, signedbv_typet(32)), u));
    add("array_large_update", index_exprt(
      with_exprt(array, from_integer(3, signedbv_typet(32)), from_integer(41, u)),
      from_integer(0, signedbv_typet(32)), u));
    add("array_repeated", index_exprt(array_of_exprt(from_integer(37, u), array_type),
      from_integer(2, signedbv_typet(32)), u));
    add("array_oob", index_exprt(array, from_integer(-1, signedbv_typet(32)), u), false);
    const struct_typet pair({struct_typet::componentt("lo", u), struct_typet::componentt("hi", u)});
    const struct_exprt record({from_integer(5, u), from_integer(29, u)}, pair);
    add("struct_member", member_exprt(record, "hi", u));
    add("struct_boolean", member_exprt(
      struct_exprt({true_exprt()}, struct_typet({struct_typet::componentt("flag", bool_typet())})),
      "flag", bool_typet()));
    const unsignedbv_typet word(32);
    const union_typet union_type({union_typet::componentt("small", u),
      union_typet::componentt("word", word)});
    add("union_padding", member_exprt(union_exprt("small", from_integer(37, u), union_type),
      "word", word), false);
    add("bool_return", true_exprt());
    add("lazy_choice", if_exprt(true_exprt(), from_integer(42, u), side_effect_expr_nondett(u, loc)), false);
    add("bool_choice", side_effect_expr_nondett(bool_typet(), loc), false);
    model.goto_functions.update();
    model.validate(validation_modet::EXCEPTION);
    stream_message_handlert messages(std::cerr);
    if (write_goto_binary(argv[1], model, messages)) throw std::runtime_error("cannot write fixture");
  } catch (const std::exception &e) {
    std::cerr << e.what() << '\n'; return 1;
  }
}
