#ifndef _BIGNUM_HPP
#define _BIGNUM_HPP

#include <deque>
#include <iostream>
#include <cassert>
#include <stdint.h>
#include <algorithm>

namespace bignum {
    using std::ios_base;
    using std::deque;
    using std::basic_istream;
    using std::basic_ostream;
    using std::streamsize;
    using std::ctype;
    using std::reverse;
    using std::swap;
    using std::use_facet;

    template <class actual_type>
    class ref_counted
    {
        typedef ref_counted<actual_type> ref_counted_type;
    public:
        ref_counted() : refcount(0U) {}

        void add_ref() { refcount++; }
        bool release() { return --refcount == 0; }

        bool is_only_ref() const { return refcount == 1; }

    protected:
        ref_counted(const ref_counted_type& o_) : refcount(0U) {}

        size_t refcount;
    };

    template <class TyUnit, class TyUnitHigher, size_t ModUnit, size_t ModUnitLog10>
    class biguint_data : public ref_counted<biguint_data<TyUnit, TyUnitHigher, ModUnit, ModUnitLog10> >
    {
        typedef TyUnit unit_type;
        typedef TyUnitHigher higher_unit_type;
        typedef deque<unit_type> array_type;
        typedef typename array_type::iterator array_type_iterator;
        typedef typename array_type::const_iterator array_type_const_iterator;
        typedef typename array_type::reverse_iterator array_type_reverse_iterator;
        typedef typename array_type::const_reverse_iterator array_type_const_reverse_iterator;
        typedef biguint_data<TyUnit, TyUnitHigher, ModUnit, ModUnitLog10> this_type;
    public:
        biguint_data() {
            ensure_data_not_empty();
        }

        biguint_data(const this_type& o_) : data(o_.data) {}

    protected:
        inline void ensure_data_not_empty() {
            if (data.empty()) data.resize(1, static_cast<unit_type>(0U));
        }

        inline void ensure_no_leading_zero() {
            while(data.size() > 1 && data.back() == 0)
            {
                data.pop_back();
            }
        }

        inline bool is_zero() const {
            return data.size() == 1 && data.back() == 0;
        }

    public:
        void add(const this_type& o_)
        {
            array_type_iterator it1 = data.begin();
            assert(it1 != data.end());
            array_type_const_iterator it2 = o_.data.begin();
            assert(it2 != data.end());
            unit_type carry = 0U;
            while(true)
            {
                unit_type sum = 0U;
                if(it1 != data.end()) sum += *it1;
                if(it2 != o_.data.end()) sum += *it2++;
                sum += carry;
                if (sum >= ModUnit)
                    sum -= ModUnit, carry = 1U;
                else
                    carry = 0U;
                if(it1 != data.end())
                    *it1++ = sum;
                else
                    it1 = ++data.insert(it1, sum);
                if(it1 == data.end() && it2 == o_.data.end() && carry == 0U) break;
            }
        }

        void minus(const this_type& o_)
        {
            array_type_iterator it1 = data.begin();
            array_type_const_iterator it2 = o_.data.begin();
            unit_type borrow = 0U;
            while(true)
            {
                if(it1 == data.end())
                {
                    if(it2 != o_.data.end() || borrow)
                    {
                        data.resize(0);
                        ensure_data_not_empty();
                    }
                    return;
                }

                unit_type to_minus = borrow;
                if(it2 != o_.data.end()) to_minus += *it2++;

                if (*it1 >= to_minus)
                    *it1++ -= to_minus, borrow = 0U;
                else
                    *it1++ += ModUnit - to_minus, borrow = 1;
            }
        }

        void multiply(const this_type& o_)
        {
            if(is_zero() || o_.is_zero())
            {
                data.clear();
                ensure_data_not_empty();
                return;
            }

            array_type tmp_data;
            swap(data, tmp_data);

            size_t sz1 = tmp_data.size(), sz2 = o_.data.size();
            data.resize(sz1 + sz2 - 1, 0U);

            for(size_t i = 0; i < sz1; i++)
            {
                higher_unit_type vi = tmp_data.at(i);
                for (size_t j = 0; j < sz2; j++)
                {
                    higher_unit_type prod = vi * o_.data.at(j);
                    array_type_iterator it = data.begin() + i + j;
                    while(prod)
                    {
                        unit_type val = static_cast<unit_type>(prod % ModUnit);
                        prod = prod / ModUnit;
                        if(it != data.end())
                        {
                            val += *it;
                            if(val > ModUnit)
                            {
                                val -= ModUnit;
                                prod++;
                            }
                            *it++ = val;
                        }
                        else
                            it = ++data.insert(it, val);
                    }
                }
            }

        }

    protected:
        void minus_may_swap(const this_type& o_)
        {
            if(less_than(o_))
            {
                this_type tmp_data(o_);
                swap(data, tmp_data.data);
                minus(tmp_data);
            }
            else
            {
                minus(o_);
            }
        }

    public:
        bool less_than(const this_type& o_) const
        {
            if(data.size() != o_.data.size())
                return data.size() < o_.data.size();
            for(array_type_const_reverse_iterator it1 = data.rbegin(), it2 = o_.data.rbegin();
                it1 != data.rend(); it1++, it2++)
            {
                if(*it1 != *it2) return *it1 < *it2;
            }
            return false;
        }

    protected:
        static size_t pow10(size_t n)
        {
            unit_type ret = 1;
            for(; n != 0; n --)
            {
                ret *= 10;
            }
            return ret;
        }

        static size_t lexical_size_for_unit(unit_type unit)
        {
            if (unit < 10U) return 1;
            else if (unit < 100U) return 2;
            else if (unit < 1000U) return 3;
            else if (unit < 10000U) return 4;
            else if (unit < 100000UL) return 5;
            else if (unit < 1000000UL) return 6;
            else if (unit < 10000000UL) return 7;
            else if (unit < 100000000UL) return 8;
            else if (unit < 1000000000UL) return 9;
            assert(false);
            return 0;
        }

        size_t lexical_size() const
        {
            return (data.size() - 1) * ModUnitLog10 + lexical_size_for_unit(data.at(data.size() - 1));
        }

    public:
        template<class TyIstrElem, class TyIstrTraits>
        bool read(basic_istream<TyIstrElem, TyIstrTraits>& istr_, ios_base::iostate& state_)
        {
            streamsize width = istr_.width();
            size_t widthlimit = width <= 0 || width >= data.max_size() ? data.max_size() : width;

            if(!helper_read_digits(istr_, state_, widthlimit))
                return false;

            return true;
        }

        template<class TyOstrElem, class TyOstrTraits>
        bool write(basic_ostream<TyOstrElem, TyOstrTraits>& ostr_, ios_base::iostate& state_)
        {
            size_t sz = lexical_size();
            streamsize width = ostr_.width();
            size_t pad = width <= 0 || width <= sz ? 0 : width - sz;

            bool pad_left = (ostr_.flags() & ios_base::adjustfield) != ios_base::left;

            if (pad_left && !helper_write_pad(ostr_, state_, pad))
                return false;

            if(!helper_write_digits(ostr_, state_))
                return false;

            if (!pad_left && !helper_write_pad(ostr_, state_, pad))
                return false;

            return true;
        };

    protected:
        template<class TyIstrElem, class TyIstrTraits>
        bool helper_read_digits(basic_istream<TyIstrElem, TyIstrTraits>& istr_, ios_base::iostate& state_, size_t widthlimit)
        {
            typedef ctype<TyIstrElem> TyCtype;
            const TyCtype& facet = use_facet<TyCtype>(istr_.getloc());

            unit_type cur_unit = 0U;
            size_t cur_unit_digitcount = 0;

            typename TyIstrTraits::int_type nextch;

            data.clear();

            for(nextch = istr_.rdbuf()->sgetc(); widthlimit > 0; widthlimit--, nextch = istr_.rdbuf()->snextc())
            {
                if(TyIstrTraits::eq_int_type(TyIstrTraits::eof(), nextch))
                {
                    state_ |= ios_base::eofbit;
                    break;
                }
                else if(!facet.is(TyCtype::digit, TyIstrTraits::to_char_type(nextch)))
                {
                    break;
                }
                else
                {
                    char ch = TyIstrTraits::to_char_type(nextch);
                    if (ch < '0' || ch > '9') ch = '0';
                    cur_unit = cur_unit * 10 + (ch - '0');
                    cur_unit_digitcount++;

                    if(cur_unit_digitcount == ModUnitLog10)
                    {
                        data.push_front(cur_unit);
                        cur_unit = 0U;
                        cur_unit_digitcount = 0;
                    }
                }
            }
            if(cur_unit_digitcount)
            {
                data.push_front(cur_unit);

                unit_type divisor = pow10(cur_unit_digitcount), rest_divisor = pow10(ModUnitLog10 - cur_unit_digitcount);

                for(array_type_iterator it1 = data.begin(), it2 = it1 + 1;
                    it2 != data.end(); it1 = it2, it2++)
                {
                    *it1 += (*it2 % rest_divisor) * divisor;
                    *it2 /= rest_divisor;
                }
            }

            if(data.empty())
            {
                state_ |= ios_base::failbit;
                ensure_data_not_empty();
                return false;
            }
            ensure_no_leading_zero();
            return true;
        }

        template<class TyOstrElem, class TyOstrTraits>
        bool helper_write_pad(basic_ostream<TyOstrElem, TyOstrTraits>& ostr_, ios_base::iostate& state_, size_t pad)
        {
            for(; pad; pad--)
            {
                if(!TyOstrTraits::eq_int_type(TyOstrTraits::eof(), ostr_.rdbuf()->sputc(ostr_.fill())))
                    continue;

                state_ |= ios_base::badbit;
                return false;
            }
            return true;
        }

        template<class TyOstrElem, class TyOstrTraits>
        bool helper_write_digits(basic_ostream<TyOstrElem, TyOstrTraits>& ostr_, ios_base::iostate& state_)
        {
            for(array_type_reverse_iterator iter = data.rbegin(); iter != data.rend(); iter++)
            {
                char unit_buf[ModUnitLog10];
                unit_type unit_val = *iter;
                bool first_unit = iter == data.rbegin();
                char* const unit_buf_end = unit_buf + ModUnitLog10;
                char* unit_buf_ptr = unit_buf;
                for(; unit_val && unit_buf_ptr != unit_buf_end; unit_buf_ptr++)
                {
                    unit_type next_val = unit_val / 10;
                    unit_type cur_digit = unit_val - next_val * 10;
                    unit_val = next_val;
                    *unit_buf_ptr = '0' + cur_digit;
                }

                if(first_unit)
                {
                    if (unit_buf_ptr == unit_buf)
                        *unit_buf_ptr++ = '0';
                }
                else
                {
                    for(; unit_buf_ptr != unit_buf_end; unit_buf_ptr++)
                    {
                        *unit_buf_ptr = '0';
                    }
                }

                reverse(unit_buf, unit_buf_ptr);
                if(ostr_.rdbuf()->sputn(unit_buf, unit_buf_ptr - unit_buf) != unit_buf_ptr - unit_buf)
                {
                    state_ |= ios_base::badbit;
                    return false;
                }
            }
            return true;
        }


    public:
        array_type data;
    };

    template <class TyUnit, class TyUnitHigher, size_t ModUnit, size_t ModUnitLog10>
    class bigint_data : public biguint_data<TyUnit, TyUnitHigher, ModUnit, ModUnitLog10>
    {
        typedef biguint_data<TyUnit, TyUnitHigher, ModUnit, ModUnitLog10> parent_type;
        typedef bigint_data<TyUnit, TyUnitHigher, ModUnit, ModUnitLog10> this_type;

        enum signal_type { POSITIVE = 1, ZERO = 0, NEGATIVE = -1};
    public:
        bigint_data() : signal(ZERO){}
        bigint_data(const this_type& o_) : parent_type(o_), signal(o_.signal) {}

    protected:
        size_t lexical_size() const
        {
            return (signal == NEGATIVE ? 1 : 0) + parent_type::lexical_size();
        }
        void update_signal_if_zero()
        {
            if(parent_type::is_zero()) signal = ZERO;
        }

        static signal_type signal_opposite(signal_type sig_)
        {
            switch(sig_)
            {
                case POSITIVE: return NEGATIVE;
                case ZERO: return ZERO;
                case NEGATIVE: return POSITIVE;
            }
        }

    public:
        void add(const this_type& o_)
        {
            if(signal == POSITIVE && o_.signal == NEGATIVE ||
               signal == NEGATIVE && o_.signal == POSITIVE)
            {
                signal = parent_type::less_than(o_) ? o_.signal : signal;

                parent_type::minus_may_swap(o_);
                update_signal_if_zero();
            }
            else
            {
                if(signal == ZERO) signal = o_.signal;
                parent_type::add(o_);
            }
        }

        void minus(const this_type& o_)
        {
            if(signal == POSITIVE && o_.signal == POSITIVE ||
               signal == NEGATIVE && o_.signal == NEGATIVE)
            {
                signal = parent_type::less_than(o_) ? signal_opposite(signal) : signal;

                parent_type::minus_may_swap(o_);
                update_signal_if_zero();
            }
            else
            {
                if(signal == ZERO) signal = signal_opposite(o_.signal);
                parent_type::add(o_);
            }
        }

        void multiply(const this_type& o_)
        {
            if(signal == ZERO || o_.signal == ZERO)
                signal = ZERO;
            else
                signal = signal == o_.signal ? POSITIVE : NEGATIVE;

            parent_type::multiply(o_);
        }

    public:
        template<class TyIstrElem, class TyIstrTraits>
        bool read(basic_istream<TyIstrElem, TyIstrTraits>& istr_, ios_base::iostate& state_)
        {
            streamsize width = istr_.width();
            size_t widthlimit = width <= 0 || width >= data.max_size() ? data.max_size() : width;

            typedef ctype<TyIstrElem> TyCtype;
            const TyCtype& facet = use_facet<TyCtype>(istr_.getloc());

            typename TyIstrTraits::int_type nextch = istr_.rdbuf()->sgetc();
            if(TyIstrTraits::eq_int_type(TyIstrTraits::eof(), nextch))
            {
                state_ |= ios_base::eofbit;
                state_ |= ios_base::failbit;
                return false;
            }
            typename TyIstrTraits::char_type ch_signal = TyIstrTraits::to_char_type(nextch);
            signal = POSITIVE;
            if(ch_signal == '+' || ch_signal == '-')
            {
                if (ch_signal == '-') signal = NEGATIVE;
                istr_.rdbuf()->snextc();
                widthlimit--;
            }

            if(!parent_type::helper_read_digits(istr_, state_, widthlimit))
                return false;

            update_signal_if_zero();

            return true;
        }

        template<class TyOstrElem, class TyOstrTraits>
        bool write(basic_ostream<TyOstrElem, TyOstrTraits>& ostr_, ios_base::iostate& state_)
        {
            size_t sz = lexical_size();
            streamsize width = ostr_.width();
            size_t pad = width <= 0 || width <= sz ? 0 : width - sz;

            bool pad_left = (ostr_.flags() & ios_base::adjustfield) != ios_base::left;

            if (pad_left && !helper_write_pad(ostr_, state_, pad))
                return false;

            if (signal == NEGATIVE)
            {
                if(ostr_.rdbuf()->sputc('-') != TyOstrTraits::to_int_type('-'))
                {
                    state_ |= ios_base::badbit;
                    return false;
                }
            }

            if(!helper_write_digits(ostr_, state_))
                return false;

            if (!pad_left && !helper_write_pad(ostr_, state_, pad))
                return false;

            return true;
        };

    protected:
        using parent_type::helper_read_digits;
        using parent_type::helper_write_pad;
        using parent_type::helper_write_digits;

    protected:
        signal_type signal;
        using parent_type::data;
    };

    template <class TyBignum>
    class basic_bignum
    {
        typedef TyBignum data_type;
        typedef basic_bignum<TyBignum> this_type;
    public:
        basic_bignum() : data(new data_type()) { data->add_ref(); }
        basic_bignum(const basic_bignum & o_) : data(o_.data) { data->add_ref(); }
        ~basic_bignum() { if(data->release()) delete data; }
        basic_bignum & operator=(const basic_bignum & o_) {
            o_.data->add_ref();
            if(data->release())
                delete data;
            data = o_.data;
        }
    protected:
        void ensure_owned_data()
        {
            if (data->is_only_ref()) return;
            data_type* new_data = new data_type(*data);
            new_data->add_ref();
            data->release();
            data = new_data;
        }

    public:
        this_type& operator+=(const this_type& o_)
        {
            ensure_owned_data();
            data->add(*o_.data);
            return *this;
        }

        this_type operator+(const this_type& o_)
        {
            this_type ret = *this;
            ret += o_;
            return ret;
        }

        this_type& operator-=(const this_type& o_)
        {
            ensure_owned_data();
            data->minus(*o_.data);
            return *this;
        }

        this_type operator-(const this_type& o_)
        {
            this_type ret = *this;
            ret -= o_;
            return ret;
        }

        this_type& operator*=(const this_type& o_)
        {
            ensure_owned_data();
            data->multiply(*o_.data);
            return *this;
        }

        this_type operator*(const this_type& o_)
        {
            this_type ret = *this;
            ret *= o_;
            return ret;
        }

    protected:
        data_type* data;

        template<class TyIstrElem, class TyIstrTraits, class TyBigNumData>
        friend inline basic_istream<TyIstrElem, TyIstrTraits>& operator >>(
                basic_istream<TyIstrElem, TyIstrTraits>& istr_,
                basic_bignum<TyBigNumData>& bignum_);

        template<class TyOstrElem, class TyOstrTraits, class TyBigNumData>
        friend inline basic_ostream<TyOstrElem, TyOstrTraits>& operator << (
                basic_ostream<TyOstrElem, TyOstrTraits>& ostr_,
                const basic_bignum<TyBigNumData>& bignum_);
    };

    template<class TyIstrElem, class TyIstrTraits, class TyBigNumData>
    inline basic_istream<TyIstrElem, TyIstrTraits>& operator >>(
            basic_istream<TyIstrElem, TyIstrTraits>& istr_,
            basic_bignum<TyBigNumData>& bignum_)
    {
        typedef basic_istream<TyIstrElem, TyIstrTraits> TyIstr;
        typedef basic_bignum<TyBigNumData> TyBigNum;

        ios_base::iostate state_ = ios_base::goodbit;
        bool changed_ = false;

        const typename TyIstr::sentry sentry(istr_);

        if(sentry)
        {
            bignum_.ensure_owned_data();

            if (bignum_.data->read(istr_, state_))
                changed_ = true;
        }
        istr_.width(0);
        if(!changed_)
            state_ |= ios_base::failbit;
        istr_.setstate(state_);
        return istr_;
    };

    template<class TyOstrElem, class TyOstrTraits, class TyBigNumData>
    inline basic_ostream<TyOstrElem, TyOstrTraits>& operator << (
            basic_ostream<TyOstrElem, TyOstrTraits>& ostr_,
            const basic_bignum<TyBigNumData>& bignum_)
    {
        typedef basic_ostream<TyOstrElem, TyOstrTraits> TyOstr;
        typedef basic_bignum<TyBigNumData> TyBigNum;

        ios_base::iostate state_ = ios_base::goodbit;
        const typename TyOstr::sentry sentry(ostr_);
        if(sentry)
        {
            if(!bignum_.data->write(ostr_, state_))
                state_ |= ios_base::badbit;
        }
        else
        {
            state_ |= ios_base::badbit;
        }
        ostr_.width(0);
        ostr_.setstate(state_);
        return ostr_;
    };


    typedef basic_bignum<biguint_data<uint16_t, uint32_t, 10000, 4> > biguint;
    typedef basic_bignum<bigint_data<uint16_t, uint32_t, 10000, 4> > bigint;
}

#endif //_BIGNUM_HPP
