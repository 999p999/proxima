local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 63) then
					if (Enum <= 31) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum == 0) then
											local A = Inst[2];
											local T = Stk[A];
											local B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										else
											for Idx = Inst[2], Inst[3] do
												Stk[Idx] = nil;
											end
										end
									elseif (Enum == 2) then
										Upvalues[Inst[3]] = Stk[Inst[2]];
									else
										local A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										local A = Inst[2];
										local Index = Stk[A];
										local Step = Stk[A + 2];
										if (Step > 0) then
											if (Index > Stk[A + 1]) then
												VIP = Inst[3];
											else
												Stk[A + 3] = Index;
											end
										elseif (Index < Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									end
								elseif (Enum == 6) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									end
								elseif (Enum > 10) then
									VIP = Inst[3];
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum > 14) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum == 16) then
										if (Stk[Inst[2]] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum > 18) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum <= 21) then
								if (Enum == 20) then
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 22) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								end
							elseif (Enum > 26) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							elseif (Stk[Inst[2]] <= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 30) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum == 32) then
										Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
									else
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									end
								elseif (Enum > 34) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 37) then
								if (Enum == 36) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum == 38) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum > 40) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								else
									local A = Inst[2];
									local Cls = {};
									for Idx = 1, #Lupvals do
										local List = Lupvals[Idx];
										for Idz = 0, #List do
											local Upv = List[Idz];
											local NStk = Upv[1];
											local DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								end
							elseif (Enum == 42) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 46) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum == 48) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 50) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 53) then
							if (Enum > 52) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum == 54) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum > 56) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 58) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						end
					elseif (Enum == 62) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						local C = Inst[4];
						local CB = A + 2;
						local Result = {Stk[A](Stk[A + 1], Stk[CB])};
						for Idx = 1, C do
							Stk[CB + Idx] = Result[Idx];
						end
						local R = Result[1];
						if R then
							Stk[CB] = R;
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					end
				elseif (Enum <= 95) then
					if (Enum <= 79) then
						if (Enum <= 71) then
							if (Enum <= 67) then
								if (Enum <= 65) then
									if (Enum == 64) then
										Stk[Inst[2]]();
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum == 66) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 69) then
								if (Enum > 68) then
									Env[Inst[3]] = Stk[Inst[2]];
								else
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum > 70) then
								local A = Inst[2];
								local B = Inst[3];
								for Idx = A, B do
									Stk[Idx] = Vararg[Idx - A];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 75) then
							if (Enum <= 73) then
								if (Enum == 72) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum == 74) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 77) then
							if (Enum == 76) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum == 78) then
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 87) then
						if (Enum <= 83) then
							if (Enum <= 81) then
								if (Enum > 80) then
									local A = Inst[2];
									local Cls = {};
									for Idx = 1, #Lupvals do
										local List = Lupvals[Idx];
										for Idz = 0, #List do
											local Upv = List[Idz];
											local NStk = Upv[1];
											local DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 82) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 85) then
							if (Enum == 84) then
								do
									return;
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 86) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 91) then
						if (Enum <= 89) then
							if (Enum > 88) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum > 90) then
							if (Stk[Inst[2]] <= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 93) then
						if (Enum > 92) then
							Stk[Inst[2]]();
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum > 94) then
						local A = Inst[2];
						do
							return Stk[A], Stk[A + 1];
						end
					else
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 118) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 111) then
					if (Enum <= 103) then
						if (Enum <= 99) then
							if (Enum <= 97) then
								if (Enum == 96) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 98) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 101) then
							if (Enum > 100) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 102) then
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						else
							local A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								local VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
						end
					elseif (Enum <= 107) then
						if (Enum <= 105) then
							if (Enum > 104) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 106) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							do
								return;
							end
						end
					elseif (Enum <= 109) then
						if (Enum == 108) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 118) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum == 110) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]] = #Stk[Inst[3]];
					end
				elseif (Enum <= 119) then
					if (Enum <= 115) then
						if (Enum <= 113) then
							if (Enum > 112) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum > 114) then
							do
								return Stk[Inst[2]];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 117) then
						if (Enum > 116) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum > 118) then
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 123) then
					if (Enum <= 121) then
						if (Enum == 120) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum > 122) then
						VIP = Inst[3];
					else
						local A = Inst[2];
						do
							return Stk[A], Stk[A + 1];
						end
					end
				elseif (Enum <= 125) then
					if (Enum == 124) then
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						local B = Inst[3];
						for Idx = A, B do
							Stk[Idx] = Vararg[Idx - A];
						end
					end
				elseif (Enum > 126) then
					Stk[Inst[2]] = not Stk[Inst[3]];
				else
					local B = Inst[3];
					local K = Stk[B];
					for Idx = B + 1, Inst[4] do
						K = K .. Stk[Idx];
					end
					Stk[Inst[2]] = K;
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!433Q0003073Q004865726F4C696203053Q005574696C7303063Q00737472696E6703063Q00666F726D617403063Q00676D6174636803083Q0073747273706C697403053Q007461626C6503063Q00636F6E63617403043Q006D656E7503073Q0063752Q72656E742Q033Q0047554903083Q00485247554947657403053Q004344734F4E03183Q00537472696E67546F4E756D6265724966506F2Q7369626C6503083Q0050616E656C536574026Q004AC0030A3Q004D61696E50616E656C41030A3Q004D61696E50616E656C52030A3Q004D61696E50616E656C58030A3Q004D61696E50616E656C5903063Q0043454E544552028Q00030D3Q004E756D6265724F665061676573026Q00224003103Q0048696465436F6E66696750616E656C73030A3Q004C6F616456617243686B030A3Q004C6F61645661724E756D030A3Q004C6F6164566172416E63030A3Q004C6F6164566172537472030A3Q00486964654672616D6573030D3Q004973506C757353686F77696E6703083Q004C6F636B4974656D03113Q00437265617465436C6F736542752Q746F6E03063Q00546970532Q65030C3Q0043726561746542752Q746F6E03093Q0043726561746542617203063Q004D616B65547803063Q004D616B654D4E030B3Q0053686F7744726F7054697003083Q004D616B6550616765030F3Q004372656174654D61696E50616E656C030C3Q0053652Q74696E677353686F77030A3Q0043726561746569636F6E030E3Q0047657450616E656C42794E616D65030B3Q0043726561746550616E656C03103Q004372656174654368696C6450616E656C03083Q0044726F70646F776E030B3Q00436865636B42752Q746F6E03063Q00536C6964657203063Q0042752Q746F6E03113Q0043726561746550616E656C4F7074696F6E030A3Q0048692Q64656E4D656E7503093Q004869646550616E656C03093Q0053686F7750616E656C03173Q004C6F616453652Q74696E67735265637572736976656C7903073Q00456E61626C656403093Q0054696D65546F44696503093Q00446566656E7369766503083Q00432Q6F6C646F776E030C3Q00446973706C61795374796C65030A3Q00506F74696F6E54797065030A3Q00506F74696F6E52616E6B03093Q00496E74652Q72757074030B3Q0047434461734F2Q66474344030E3Q004F2Q6647434461734F2Q6647434403133Q00437265617465415250616E656C4F7074696F6E03143Q00437265617465415250616E656C4F7074696F6E7300F84Q00473Q00024Q000D000200013Q00126E000300013Q00204300040003000200126E000500033Q00204300050005000400126E000600033Q00204300060006000500126E000700063Q00126E000800073Q0020430008000800082Q00240009000A4Q004D000B6Q004D000C3Q00022Q004D000D5Q001057000C0009000D2Q004D000D5Q001057000C000A000D0010570002000B000C00065E000D3Q000100012Q00763Q000C3Q0010570002000C000D00065E000D0001000100012Q00763Q00023Q0010570001000D000D000220000D00024Q000D000E000D4Q0059000E00010002002043000F0004000E2Q0024001000113Q00065E00120003000100042Q00763Q00104Q00763Q00024Q00763Q00114Q00763Q000C3Q0010570002000F00122Q004D00126Q004D00136Q004D00145Q001274001500103Q001274001600153Q001274001700153Q001274001800163Q003069000C00140016001057000C00130018001057000C00120017001057000C00110016003069000C0017001800065E00160004000100012Q00763Q00143Q001057000C0019001600065E00160005000100022Q00763Q00114Q00763Q000C3Q001057000C001A001600065E00160006000100022Q00763Q00114Q00763Q000C3Q001057000C001B001600065E00160007000100022Q00763Q00114Q00763Q000C3Q001057000C001C001600065E00160008000100022Q00763Q00114Q00763Q000C3Q001057000C001D001600065E00160009000100012Q00763Q000C3Q001057000C001E001600065E0016000A000100022Q00763Q000C4Q00763Q00143Q001057000C001F00160002200016000B3Q001057000C002000160002200016000C3Q001057000C0021001600065E0016000D000100012Q00763Q000B3Q001057000C0022001600065E0016000E000100032Q00763Q000D4Q00763Q000C4Q00763Q000B3Q001057000C002300160002200016000F3Q001057000C0024001600065E00160010000100012Q00763Q000C3Q001057000C0025001600065E00160011000100012Q00763Q000C3Q001057000C0026001600065E00160012000100012Q00763Q000B3Q001057000C0027001600065E00160013000100042Q00763Q000E4Q00763Q000D4Q00763Q000C4Q00763Q00153Q001057000C0028001600065E00160014000100022Q00763Q000E4Q00763Q000C3Q001057000C002900162Q005100125Q00065E00120015000100012Q00763Q000C3Q001057000C002A001200065E00120016000100032Q00763Q00024Q00763Q000C4Q00763Q000E3Q001057000C002B00122Q004D00125Q00204300130003000B00065E00140017000100022Q00763Q00124Q00763Q000E3Q0010570013002C001400204300130003000B00065E00140018000100052Q00763Q000E4Q00763Q000C4Q00763Q000A4Q00763Q00094Q00763Q00123Q0010570013002D001400204300130003000B00065E00140019000100022Q00763Q000C4Q00763Q00123Q0010570013002E001400065E0013001A000100012Q00763Q000F3Q00065E0014001B000100082Q00763Q000C4Q00763Q000D4Q00763Q00134Q00763Q000A4Q00763Q00074Q00763Q00054Q00763Q000B4Q00763Q00093Q00065E0015001C000100072Q00763Q000C4Q00763Q000D4Q00763Q00134Q00763Q000A4Q00763Q00074Q00763Q00094Q00763Q000B3Q00065E0016001D000100072Q00763Q000C4Q00763Q000D4Q00763Q00134Q00763Q000A4Q00763Q00074Q00763Q000B4Q00763Q00093Q00065E0017001E000100032Q00763Q000C4Q00763Q000D4Q00763Q000B4Q004D00183Q00040010570018002F001600105700180030001500105700180031001400105700180032001700204300190003000B00065E001A001F000100012Q00763Q00183Q00105700190033001A2Q004D00195Q001057000C0034001900204300190003000B00065E001A0020000100012Q00763Q000C3Q00105700190035001A00204300190003000B00065E001A0021000100012Q00763Q000C3Q00105700190036001A00204300190003000B00204300190019003300065E001A0022000100032Q00763Q000C4Q00763Q000F4Q00763Q00103Q001057000C0037001A00065E001A0023000100012Q00763Q00053Q00065E001B0024000100012Q00763Q00053Q00065E001C0025000100012Q00763Q00053Q00065E001D0026000100012Q00763Q00054Q004D001E3Q000A00065E001F0027000100012Q00763Q00193Q001057001E0038001F00065E001F0028000100012Q00763Q00193Q001057001E0039001F00065E001F0029000100012Q00763Q00193Q001057001E003A001F00065E001F002A000100012Q00763Q00193Q001057001E003B001F00065E001F002B000100012Q00763Q00193Q001057001E003C001F00065E001F002C000100012Q00763Q00193Q001057001E003D001F00065E001F002D000100012Q00763Q00193Q001057001E003E001F00065E001F002E000100012Q00763Q00193Q001057001E003F001F00065E001F002F000100032Q00763Q00194Q00763Q001A4Q00763Q001B3Q001057001E0040001F00065E001F0030000100032Q00763Q00194Q00763Q001C4Q00763Q001D3Q001057001E0041001F00065E001F0031000100012Q00763Q001E3Q001057000C0042001F00065E001F0032000100062Q00763Q00074Q00763Q00024Q00763Q001E4Q00763Q00064Q00763Q00084Q00763Q000C3Q001057000C0043001F2Q0051001A6Q006A3Q00013Q00338Q00034Q00638Q00733Q00024Q006A3Q00019Q003Q00034Q00638Q00733Q00024Q006A3Q00017Q00033Q0003083Q00746F737472696E6703043Q006D61746803063Q0072616E646F6D00073Q00126E3Q00013Q00126E000100023Q0020430001000100032Q0032000100014Q00605Q00022Q00733Q00024Q006A3Q00017Q00103Q0003113Q0047657453617665645661726961626C6573030D3Q0050616E656C53652Q74696E6773030A3Q004C6F6164566172416E63030A3Q004D61696E50616E656C4103063Q0043454E544552030A3Q004D61696E50616E656C52030A3Q004C6F61645661724E756D030A3Q004D61696E50616E656C58028Q00025Q0088B3C0025Q0088B340030A3Q004D61696E50616E656C59030A3Q004C6F616456617243686B030B3Q00485253746172745061676503073Q0047656E6572616C03053Q005061676573002F4Q00633Q00013Q0020435Q00012Q00593Q000100022Q00028Q00637Q0020435Q00020006683Q000B0001000100047B3Q000B00012Q00638Q004D00015Q0010573Q000200012Q00637Q0020435Q00022Q00023Q00024Q00633Q00033Q0020335Q0003001274000200043Q001274000300054Q002B3Q000300012Q00633Q00033Q0020335Q0003001274000200063Q001274000300054Q002B3Q000300012Q00633Q00033Q0020335Q0007001274000200083Q001274000300093Q0012740004000A3Q0012740005000B4Q002B3Q000500012Q00633Q00033Q0020335Q00070012740002000C3Q001274000300093Q0012740004000A3Q0012740005000B4Q002B3Q000500012Q00633Q00033Q0020335Q000D0012740002000E3Q0012740003000F4Q002B3Q000300012Q00633Q00034Q004D00015Q0010573Q001000012Q006A3Q00017Q00023Q0003053Q00706169727303043Q004869646501093Q00126E000100014Q006300026Q003A00010002000300047B3Q000600010020330006000500022Q002A000600020001000614000100040001000200047B3Q000400012Q006A3Q00017Q00043Q0003043Q007479706503063Q00737472696E6703023Q004F6E2Q033Q004F2Q66031C4Q006300036Q006B0003000300010006620003000E00013Q00047B3Q000E000100126E000300014Q006300046Q006B0004000400012Q005600030002000200262F0003000E0001000200047B3Q000E00012Q006300036Q006B000300030001002653000300120001000300047B3Q001200012Q006300036Q006B00030003000100262F000300170001000400047B3Q001700012Q0063000300014Q006300046Q006B0004000400012Q003E00030001000400047B3Q001B00012Q0063000300014Q003E0003000100022Q006300036Q003E0003000100022Q006A3Q00017Q00023Q0003043Q007479706503063Q006E756D626572051C4Q006300056Q006B0005000500010006620005001700013Q00047B3Q0017000100126E000500014Q006300066Q006B0006000600012Q005600050002000200262F000500170001000200047B3Q001700012Q006300056Q006B00050005000100067C000300170001000500047B3Q001700012Q006300056Q006B00050005000100067C000500170001000400047B3Q001700012Q0063000500014Q006300066Q006B0006000600012Q003E00050001000600047B3Q001B00012Q0063000500014Q003E0005000100022Q006300056Q003E0005000100022Q006A3Q00017Q000B3Q0003043Q007479706503063Q00737472696E6703063Q0043454E5445522Q033Q00544F5003063Q00424F2Q544F4D03043Q004C45465403053Q00524947485403073Q00544F504C45465403083Q00544F505249474854030A3Q00424F2Q544F4D4C454654030B3Q00424F2Q544F4D524947485403384Q006300036Q006B0003000300010006620003000E00013Q00047B3Q000E000100126E000300014Q006300046Q006B0004000400012Q005600030002000200262F0003000E0001000200047B3Q000E00012Q006300036Q006B0003000300010026530003002E0001000300047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000400047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000500047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000600047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000700047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000800047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000900047B3Q002E00012Q006300036Q006B0003000300010026530003002E0001000A00047B3Q002E00012Q006300036Q006B00030003000100262F000300330001000B00047B3Q003300012Q0063000300014Q006300046Q006B0004000400012Q003E00030001000400047B3Q003700012Q0063000300014Q003E0003000100022Q006300036Q003E0003000100022Q006A3Q00017Q00023Q0003043Q007479706503063Q00737472696E6703144Q006300036Q006B0003000300010006620003000F00013Q00047B3Q000F000100126E000300014Q006300046Q006B0004000400012Q005600030002000200262F0003000F0001000200047B3Q000F00012Q0063000300014Q006300046Q006B0004000400012Q003E00030001000400047B3Q001300012Q0063000300014Q003E0003000100022Q006300036Q003E0003000100022Q006A3Q00017Q00043Q0003053Q00706169727303053Q00506167657303043Q004869646503053Q00506167654601103Q00126E000100014Q006300025Q0020430002000200022Q003A00010002000300047B3Q000900010006620005000900013Q00047B3Q000900010020330006000500032Q002A000600020001000614000100050001000200047B3Q000500012Q006300015Q0020430001000100040020330001000100032Q002A0001000200012Q006A3Q00017Q00033Q0003053Q00506167654603073Q00497353686F776E03053Q00706169727301154Q006300015Q0020430001000100010020330001000100022Q00560001000200020006620001000800013Q00047B3Q000800012Q0070000100014Q0073000100023Q00126E000100034Q0063000200014Q003A00010002000300047B3Q001200010020330006000500022Q00560006000200020006620006001200013Q00047B3Q001200012Q0070000600014Q0073000600023Q0006140001000C0001000200047B3Q000C00012Q006A3Q00017Q00053Q0003073Q0044697361626C6503083Q00536574416C706861026Q33D33F03063Q00456E61626C65026Q00F03F030E3Q0006620002000800013Q00047B3Q000800010020330003000100012Q002A000300020001002033000300010002001274000500034Q002B00030005000100047B3Q000D00010020330003000100042Q002A000300020001002033000300010002001274000500054Q002B0003000500012Q006A3Q00017Q000C3Q00030B3Q004372656174654672616D6503063Q0042552Q544F4E03073Q0053657453697A6503083Q00536574506F696E7403103Q005365744E6F726D616C54657874757265032C3Q00496E746572666163655C42752Q746F6E735C55492D50616E656C2D4D696E696D697A6542752Q746F6E2D557003133Q00536574486967686C696768745465787475726503333Q00496E746572666163655C42752Q746F6E735C55492D50616E656C2D4D696E696D697A6542752Q746F6E2D486967686C6967687403103Q0053657450757368656454657874757265032E3Q00496E746572666163655C42752Q746F6E735C55492D50616E656C2D4D696E696D697A6542752Q746F6E2D446F776E03123Q0053657444697361626C65645465787475726503323Q00496E746572666163655C42752Q746F6E735C55492D50616E656C2D4D696E696D697A6542752Q746F6E2D44697361626C6564071C3Q00126E000700013Q001274000800024Q0024000900094Q000D000A00014Q00350007000A00020020330008000700032Q000D000A00024Q000D000B00034Q002B0008000B00010020330008000700042Q000D000A00044Q000D000B00054Q000D000C00064Q002B0008000C0001002033000800070005001274000A00064Q002B0008000A0001002033000800070007001274000A00084Q002B0008000A0001002033000800070009001274000A000A4Q002B0008000A000100203300080007000B001274000A000C4Q002B0008000A00012Q0073000700024Q006A3Q00017Q00103Q00030B3Q0047616D65542Q6F6C74697003083Q005365744F776E6572030B3Q00414E43484F525F4E4F4E4503093Q00476574506172656E74030D3Q004765744F626A65637454797065030B3Q005363726F2Q6C4672616D6503113Q00476574452Q666563746976655363616C6503083Q005549506172656E7403083Q004765745269676874025Q00406F4003083Q00536574506F696E7403083Q00544F50524947485403073Q00544F504C454654028Q0003073Q005365745465787403073Q004765744E616D6501483Q00126E000100013Q0020330001000100022Q000D00035Q001274000400034Q002B00010004000100203300013Q00042Q00560001000200020020330002000100042Q00560002000200020006620002001A00013Q00047B3Q001A00010020330002000100042Q00560002000200020020330002000200052Q005600020002000200262F0002001A0001000600047B3Q001A000100203300023Q00042Q00560002000200020020330002000200042Q00560002000200020020330002000200042Q00560002000200020020330002000200042Q00560002000200022Q000D000100023Q0020330002000100072Q005600020002000200126E000300083Q0020330003000300072Q005600030002000200126E000400013Q0020330004000400072Q005600040002000200126E000500083Q0020330005000500092Q00560005000200022Q00340005000500030020330006000100092Q00560006000200022Q00340006000600022Q003C0005000500060010270006000A0004000650000500360001000600047B3Q0036000100126E000600013Q00203300060006000B0012740008000C4Q000D000900013Q001274000A000D3Q001274000B000E3Q001274000C000E4Q002B0006000C000100047B3Q003E000100126E000600013Q00203300060006000B0012740008000D4Q000D000900013Q001274000A000C3Q001274000B000E3Q001274000C000E4Q002B0006000C000100126E000600013Q00203300060006000F2Q006300085Q00203300093Q00102Q00560009000200022Q006B0008000800092Q00240009000C4Q0070000D00014Q002B0006000D00012Q006A3Q00017Q00153Q00030B3Q004372656174654672616D6503063Q0042752Q746F6E03153Q00554950616E656C42752Q746F6E54656D706C61746503073Q0053657453697A6503083Q00536574506F696E7403103Q0053657448697452656374496E73657473028Q0003073Q005365745465787403013Q006603103Q00437265617465466F6E74537472696E6703073Q00415254574F524B030E3Q0047616D65466F6E744E6F726D616C03083Q005365745769647468030E3Q00476574537472696E675769647468026Q00344003073Q004765744E616D6503093Q0053657453637269707403073Q004F6E456E74657203063Q00546970532Q6503073Q004F6E4C6561766503103Q0047616D65542Q6F6C7469705F486964650C403Q00126E000C00013Q001274000D00024Q0063000E6Q0059000E000100022Q000D000F00023Q001274001000034Q0035000C001000022Q0063000D00014Q003E000D0001000C002033000D000C00042Q000D000F00074Q000D001000084Q002B000D00100001002033000D000C00052Q000D000F00044Q000D001000054Q000D001100064Q002B000D00110001002033000D000C0006001274000F00073Q001274001000073Q001274001100073Q001274001200074Q002B000D00120001002033000D000C00082Q000D000F00034Q002B000D000F0001002033000D000C000A2Q0024000F000F3Q0012740010000B3Q0012740011000C4Q0035000D00110002001057000C0009000D002043000D000C0009002033000D000D00082Q000D000F00034Q002B000D000F0001000E0C0007002B0001000700047B3Q002B0001002033000D000C000D2Q000D000F00074Q002B000D000F000100047B3Q00310001002033000D000C000D002043000F000C0009002033000F000F000E2Q0056000F00020002002009000F000F000F2Q002B000D000F00012Q0063000D00023Q002033000E000C00102Q0056000E000200022Q003E000D000E000A002033000D000C0011001274000F00124Q0063001000013Q0020430010001000132Q002B000D00100001002033000D000C0011001274000F00143Q00126E001000154Q002B000D001000012Q0073000C00024Q006A3Q00017Q000B3Q00030D3Q004372656174655465787475726503063Q00424F52444552030A3Q005365745465787475726503073Q0053657453697A6503083Q00536574506F696E74030E3Q00536574566572746578436F6C6F72030B3Q004D61696E54657874757265030B3Q00536574546578432Q6F7264020AD7A3703D0AB73F026Q00F03F028Q000B1D3Q002033000B000200012Q0024000D000D3Q001274000E00024Q0035000B000E0002002033000C000B00032Q000D000E000A4Q002B000C000E0001002033000C000B00042Q000D000E00034Q000D000F00044Q002B000C000F0001002033000C000B00052Q000D000E00054Q002B000C000E0001002033000C000B00062Q000D000E00064Q000D000F00074Q000D001000084Q000D001100094Q002B000C0011000100262F0001001C0001000700047B3Q001C0001002033000C000B0008001274000E00093Q001274000F000A3Q0012740010000B3Q0012740011000A4Q002B000C001100012Q006A3Q00017Q000E3Q0003073Q0063752Q72656E7403073Q004765744E616D6503013Q0079026Q003940025Q00807DC0026Q004AC003013Q0078025Q0020774003103Q00437265617465466F6E74537472696E6703073Q00415254574F524B030E3Q0047616D65466F6E744E6F726D616C03083Q00536574506F696E7403073Q00544F504C45465403073Q005365745465787405463Q0006680004000F0001000100047B3Q000F00012Q006300055Q0020430005000500010020330006000100022Q00560006000200022Q006B0005000500062Q006300065Q0020430006000600010020330007000100022Q00560007000200022Q006B000600060007002043000600060003002008000600060004001057000500030006000668000300270001000100047B3Q00270001000668000400270001000100047B3Q002700012Q006300055Q0020430005000500010020330006000100022Q00560006000200022Q006B00050005000600204300050005000300265B000500270001000500047B3Q002700012Q006300055Q0020430005000500010020330006000100022Q00560006000200022Q006B0005000500060030690005000300062Q006300055Q0020430005000500010020330006000100022Q00560006000200022Q006B00050005000600306900050007000800062E0005002F0001000400047B3Q002F00012Q006300055Q0020430005000500010020330006000100022Q00560006000200022Q006B00050005000600204300050005000300062E000600370001000300047B3Q003700012Q006300065Q0020430006000600010020330007000100022Q00560007000200022Q006B0006000600070020430006000600070020330007000100092Q0024000900093Q001274000A000A3Q001274000B000B4Q00350007000B000200203300080007000C001274000A000D4Q000D000B00064Q000D000C00054Q002B0008000C000100203300080007000E2Q000D000A00024Q002B0008000A00012Q0073000700024Q006A3Q00017Q001C3Q00030B3Q004372656174654672616D6503063Q0042752Q746F6E03043Q0053686F7703073Q0053657453697A6503083Q00536574416C706861026Q00F03F03083Q00536574506F696E7403013Q0074030D3Q0043726561746554657874757265030A3Q004241434B47524F554E44030C3Q00536574412Q6C506F696E7473030F3Q00536574436F6C6F7254657874757265026Q33D33F028Q00029A5Q99E93F026Q66E63F03043Q004869646503013Q007303013Q006603103Q00437265617465466F6E74537472696E6703073Q00415254574F524B030E3Q0047616D65466F6E744E6F726D616C03043Q004C454654026Q00204003073Q005365745465787403093Q0053657453637269707403073Q004F6E456E74657203073Q004F6E4C65617665095B3Q00126E000900013Q001274000A00024Q0024000B000B4Q000D000C00034Q00350009000C00022Q0063000A6Q003E000A00010009002033000A000900032Q002A000A00020001002033000A000900042Q000D000C00074Q000D000D00084Q002B000A000D0001002033000A00090005001274000C00064Q002B000A000C0001002033000A000900072Q000D000C00044Q000D000D00054Q000D000E00064Q002B000A000E0001002033000A000900092Q0024000C000C3Q001274000D000A4Q0035000A000D000200105700090008000A002043000A00090008002033000A000A000B2Q002A000A00020001002043000A00090008002033000A000A000C001274000C000D3Q001274000D000D3Q001274000E000E3Q001274000F000F4Q002B000A000F0001002043000A00090008002033000A000A0005001274000C00104Q002B000A000C0001002043000A00090008002033000A000A00112Q002A000A00020001002033000A000900092Q0024000C000C3Q001274000D000A4Q0035000A000D000200105700090012000A002043000A00090012002033000A000A000B2Q002A000A00020001002043000A00090012002033000A000A000C001274000C000D3Q001274000D000D3Q001274000E000E3Q001274000F000F4Q002B000A000F0001002043000A00090012002033000A000A00112Q002A000A00020001002033000A000900142Q0024000C000C3Q001274000D00153Q001274000E00164Q0035000A000E000200105700090013000A002043000A00090013002033000A000A0007001274000C00173Q001274000D00183Q001274000E000E4Q002B000A000E0001002043000A00090013002033000A000A00192Q000D000C00024Q002B000A000C0001002033000A0009001A001274000C001B3Q00065E000D3Q000100012Q00763Q00094Q002B000A000D0001002033000A0009001A001274000C001C3Q00065E000D0001000100012Q00763Q00094Q002B000A000D00012Q000D000A00093Q002043000B000900122Q007A000A00034Q006A3Q00013Q00023Q00023Q0003013Q007403043Q0053686F7700054Q00637Q0020435Q00010020335Q00022Q002A3Q000200012Q006A3Q00017Q00023Q0003013Q007403043Q004869646500054Q00637Q0020435Q00010020335Q00022Q002A3Q000200012Q006A3Q00017Q000E3Q00030B3Q0047616D65542Q6F6C74697003083Q005365744F776E6572030B3Q00414E43484F525F4E4F4E4503093Q00476574506172656E7403113Q00476574452Q666563746976655363616C6503083Q005549506172656E7403083Q004765745269676874025Q00406F4003083Q00536574506F696E7403083Q00544F50524947485403073Q00544F504C454654028Q0003073Q005365745465787403073Q004765744E616D6501373Q00126E000100013Q0020330001000100022Q000D00035Q001274000400034Q002B00010004000100203300013Q00042Q00560001000200020020330001000100042Q00560001000200020020330002000100052Q005600020002000200126E000300063Q0020330003000300052Q005600030002000200126E000400013Q0020330004000400052Q005600040002000200126E000500063Q0020330005000500072Q00560005000200022Q00340005000500030020330006000100072Q00560006000200022Q00340006000600022Q003C000500050006001027000600080004000650000500250001000600047B3Q0025000100126E000600013Q0020330006000600090012740008000A4Q000D000900013Q001274000A000B3Q001274000B000C3Q001274000C000C4Q002B0006000C000100047B3Q002D000100126E000600013Q0020330006000600090012740008000B4Q000D000900013Q001274000A000A3Q001274000B000C3Q001274000C000C4Q002B0006000C000100126E000600013Q00203300060006000D2Q006300085Q00203300093Q000E2Q00560009000200022Q006B0008000800092Q00240009000C4Q0070000D00014Q002B0006000D00012Q006A3Q00017Q00213Q0003013Q007C030B3Q004372656174654672616D6503053Q004672616D6503053Q005061676546030C3Q00536574412Q6C506F696E747303043Q004869646503013Q007303103Q00437265617465466F6E74537472696E6703073Q00415254574F524B03133Q0047616D65466F6E744E6F726D616C4C6172676503083Q00536574506F696E7403073Q00544F504C454654025Q00406240026Q0030C003073Q005365745465787403073Q0063752Q72656E7403073Q004765744E616D6503013Q0079026Q003BC003013Q007803043Q006D656E7503023Q002E7303063Q004D616B654D4E026Q001040025Q00406040026Q00344003093Q0053657453637269707403063Q004F6E53686F7703063Q004F6E4869646503073Q004F6E436C69636B03053Q007461626C6503063Q00696E7365727403053Q00506167657303794Q006300035Q00064C000200050001000300047B3Q0005000100062E000300090001000100047B3Q000900012Q000D000300023Q001274000400014Q000D000500014Q006D00030003000500126E000400023Q001274000500034Q000D000600024Q0063000700014Q00590007000100022Q006D0006000600072Q0063000700023Q0020430007000700042Q00350004000700022Q0063000500024Q003E0005000300040020330005000400052Q0063000700023Q0020430007000700042Q002B0005000700010020330005000400062Q002A0005000200010020330005000400082Q0024000700073Q001274000800093Q0012740009000A4Q003500050009000200105700040007000500204300050004000700203300050005000B0012740007000C3Q0012740008000D3Q0012740009000E4Q002B00050009000100204300050004000700203300050005000F2Q000D000700014Q002B0005000700012Q0063000500023Q0020430005000500100020330006000400112Q00560006000200022Q004D00073Q000200306900070012001300306900070014000D2Q003E0005000600072Q0063000500014Q00590005000100020006620005005C00013Q00047B3Q005C00012Q0063000600023Q0020430006000600150020330007000400112Q00560007000200022Q0063000800024Q000D000900053Q001274000A00164Q006D00090009000A2Q0063000A00023Q002033000A000A00172Q000D000C00054Q000D000D00014Q0063000E00023Q002043000E000E0004001274000F000C3Q001274001000184Q0063001100033Q001274001200193Q0012740013001A4Q0077000A0013000B2Q003E00080009000B2Q003E00060007000A2Q0063000600024Q006B00060006000300203300060006001B0012740008001C3Q00065E00093Q000100022Q004F3Q00024Q00763Q00054Q002B0006000900012Q0063000600024Q006B00060006000300203300060006001B0012740008001D3Q00065E00090001000100022Q004F3Q00024Q00763Q00054Q002B0006000900012Q0063000600023Q0020430006000600150020330007000400112Q00560007000200022Q006B0006000600070006620006006E00013Q00047B3Q006E00012Q0063000600023Q0020430006000600150020330007000400112Q00560007000200022Q006B00060006000700203300060006001B0012740008001E3Q00065E00090002000100022Q004F3Q00024Q00763Q00034Q002B00060009000100126E0006001F3Q0020430006000600202Q0063000700023Q0020430007000700212Q000D000800044Q002B0006000800012Q0063000600033Q00200800060006001A2Q0002000600034Q0073000400024Q006A3Q00013Q00033Q00023Q0003023Q002E7303043Q0053686F7700084Q00638Q0063000100013Q001274000200014Q006D0001000100022Q006B5Q00010020335Q00022Q002A3Q000200012Q006A3Q00017Q00023Q0003023Q002E7303043Q004869646500084Q00638Q0063000100013Q001274000200014Q006D0001000100022Q006B5Q00010020335Q00022Q002A3Q000200012Q006A3Q00017Q00043Q00030A3Q00486964654672616D657303053Q00506167654603043Q0053686F77030B3Q00485253746172745061676500104Q00637Q0020335Q00012Q002A3Q000200012Q00637Q0020435Q00020020335Q00032Q002A3Q000200012Q00638Q0063000100014Q006B5Q00010020335Q00032Q002A3Q000200012Q00638Q0063000100013Q0010573Q000400012Q006A3Q00017Q004C3Q00030B3Q004372656174654672616D6503053Q004672616D6503053Q00506167654603073Q0053657453697A65025Q00508440025Q0030814003043Q0048696465030E3Q005365744672616D6553747261746103113Q0046552Q4C5343522Q454E5F4449414C4F4703123Q00536574436C616D706564546F5363722Q656E03123Q00536574436C616D7052656374496E73657473025Q00407F40025Q00407FC0025Q00C072C0025Q00C07240030B3Q00456E61626C654D6F757365030A3Q005365744D6F7661626C65030F3Q005265676973746572466F7244726167030A3Q004C65667442752Q746F6E03093Q00536574536372697074030B3Q004F6E447261675374617274030B3Q0053746172744D6F76696E67030A3Q004F6E4472616753746F7003013Q0074030D3Q0043726561746554657874757265030A3Q004241434B47524F554E44030C3Q00536574412Q6C506F696E7473030F3Q00536574436F6C6F7254657874757265029A5Q99A93F026Q66E63F03093Q00437265617465426172030B3Q00462Q6F7454657874757265026Q00484003063Q00424F2Q544F4D026Q00F03F03533Q00496E746572666163655C414348494556454D454E544652414D455C55492D4775696C64416368696576656D656E742D50617263686D656E742D486F72697A6F6E74616C2D44657361747572617465642E706E67030B3Q004D61696E54657874757265025Q00707F4003083Q00544F505249474854029A5Q99B93F030B3Q004D656E7554657874757265025Q00C0624003073Q00544F504C45465403063Q004F6E53686F7703023Q006D7403103Q00437265617465466F6E74537472696E6703073Q00415254574F524B03133Q0047616D65466F6E744E6F726D616C4C6172676503083Q00536574506F696E74026Q003040026Q0030C003073Q0053657454657874030C3Q004865726F526F746174696F6E030C3Q0043726561746542752Q746F6E030E3Q0052656C6F6164554942752Q746F6E03063Q0052656C6F6164030B3Q00424F2Q544F4D5249474854026Q002440028Q00026Q00394003E33Q00596F7572205549206E2Q65647320746F2062652072656C6F6164656420666F7220736F6D65206F6620746865206368616E67657320746F2074616B6520652Q666563742E7C6E7C6E596F7520646F6E2774206861766520746F20636C69636B207468652072656C6F61642062752Q746F6E20692Q6D6564696174656C792062757420796F7520646F206E2Q656420746F20636C69636B206974207768656E20796F752061726520646F6E65206D616B696E67206368616E67657320616E6420796F752077616E7420746865206368616E67657320746F2074616B6520652Q666563742E03073Q004F6E436C69636B03083Q0052656C6F6164554903013Q006603133Q0047616D65466F6E744E6F726D616C536D612Q6C03093Q00536574486569676874026Q002Q4003053Q00524947485403043Q004C454654026Q0024C0031D3Q00596F7572205549206E2Q65647320746F2062652072656C6F616465642E03113Q00437265617465436C6F736542752Q746F6E026Q003E40030A3Q00486964654672616D6573030F3Q004372656174654D61696E50616E656C0001B23Q00126E000100013Q001274000200024Q006300036Q0024000400044Q00350001000400022Q0063000200013Q001057000200030001002033000200010004001274000400053Q001274000500064Q002B0002000500010020330002000100072Q002A000200020001002033000200010008001274000400094Q002B00020004000100203300020001000A2Q0070000400014Q002B00020004000100203300020001000B0012740004000C3Q0012740005000D3Q0012740006000E3Q0012740007000F4Q002B0002000700010020330002000100102Q0070000400014Q002B0002000400010020330002000100112Q0070000400014Q002B000200040001002033000200010012001274000400134Q002B000200040001002033000200010014001274000400153Q0020430005000100162Q002B000200050001002033000200010014001274000400173Q00065E00053Q000100022Q00763Q00014Q004F3Q00014Q002B0002000500010020330002000100192Q0024000400043Q0012740005001A4Q003500020005000200105700010018000200204300020001001800203300020002001B2Q002A00020002000100204300020001001800203300020002001C0012740004001D3Q0012740005001D3Q0012740006001D3Q0012740007001E4Q002B0002000700012Q0063000200013Q00203300020002001F001274000400204Q000D000500013Q001274000600053Q001274000700213Q001274000800223Q0012740009001E3Q001274000A001E3Q001274000B001E3Q001274000C00233Q001274000D00244Q002B0002000D00012Q0063000200013Q00203300020002001F001274000400254Q000D000500013Q0012740006000C3Q001274000700263Q001274000800273Q0012740009001E3Q001274000A001E3Q001274000B001E3Q001274000C00284Q002B0002000C00012Q0063000200013Q00203300020002001F001274000400294Q000D000500013Q0012740006002A3Q001274000700263Q0012740008002B3Q001274000900283Q001274000A00283Q001274000B00283Q001274000C00234Q002B0002000C00010020330002000100140012740004002C3Q00065E00050001000100022Q00763Q00014Q004F3Q00014Q002B00020005000100203300020001002E2Q0024000400043Q0012740005002F3Q001274000600304Q00350002000600020010570001002D000200204300020001002D0020330002000200310012740004002B3Q001274000500323Q001274000600334Q002B00020006000100204300020001002D002033000200020034001274000400354Q002B0002000400012Q0063000200013Q002033000200020036001274000400374Q000D000500013Q001274000600383Q001274000700393Q001274000800333Q0012740009003A3Q001274000A003B3Q001274000B003C4Q0070000C00013Q001274000D003D4Q00350002000D00020020330003000200140012740005003E3Q00126E0006003F4Q002B00030006000100203300030002002E2Q0024000500053Q0012740006002F3Q001274000700414Q0035000300070002001057000200400003002043000300020040002033000300030042001274000500434Q002B000300050001002043000300020040002033000300030031001274000500444Q000D000600023Q001274000700453Q001274000800463Q0012740009003B4Q002B000300090001002043000300020040002033000300030034001274000500474Q002B0003000500010020430003000200400020330003000300072Q002A0003000200012Q0063000300013Q0020330003000300482Q000D000500013Q001274000600493Q001274000700493Q001274000800273Q0012740009003B3Q001274000A003B4Q00350003000A00020020330004000300140012740006003E4Q0063000700013Q00204300070007004A2Q002B0004000700012Q0063000400013Q0030690004004B004C2Q0073000100024Q006A3Q00013Q00023Q00083Q0003123Q0053746F704D6F76696E674F7253697A696E67030D3Q0053657455736572506C61636564030A3Q004D61696E50616E656C4103013Q005F030A3Q004D61696E50616E656C52030A3Q004D61696E50616E656C58030A3Q004D61696E50616E656C5903083Q00476574506F696E7400144Q00637Q0020335Q00012Q002A3Q000200012Q00637Q0020335Q00022Q007000026Q002B3Q000200012Q00633Q00014Q0063000100014Q0063000200014Q0063000300014Q006300045Q0020330004000400082Q003A000400020008001057000300070008001057000200060007001057000100050006001258000500043Q0010573Q000300042Q006A3Q00017Q00073Q00030E3Q00436C656172412Q6C506F696E747303083Q00536574506F696E74030A3Q004D61696E50616E656C4103083Q005549506172656E74030A3Q004D61696E50616E656C52030A3Q004D61696E50616E656C58030A3Q004D61696E50616E656C5900104Q00637Q0020335Q00012Q002A3Q000200012Q00637Q0020335Q00022Q0063000200013Q00204300020002000300126E000300044Q0063000400013Q0020430004000400052Q0063000500013Q0020430005000500062Q0063000600013Q0020430006000600072Q002B3Q000600012Q006A3Q00017Q00063Q00030D3Q004973506C757353686F77696E67030A3Q00486964654672616D657303103Q0048696465436F6E66696750616E656C7303053Q00506167654603043Q0053686F77030B3Q004852537461727450616765001A4Q00637Q0020335Q00012Q00563Q000200020006623Q000C00013Q00047B3Q000C00012Q00637Q0020335Q00022Q002A3Q000200012Q00637Q0020335Q00032Q002A3Q0002000100047B3Q001300012Q00637Q0020335Q00022Q002A3Q000200012Q00637Q0020435Q00040020335Q00052Q002A3Q000200012Q00638Q006300015Q0020430001000100062Q006B5Q00010020335Q00052Q002A3Q000200012Q006A3Q00017Q000E3Q00030E3Q00496E74652Q72757074436865636B03073Q004C696253747562030D3Q004C6962444249636F6E2D312E3003113Q004C69624461746142726F6B65722D312E31030D3Q004E6577446174614F626A65637403043Q0074797065030B3Q006461746120736F7572636503043Q0074657874030C3Q004865726F526F746174696F6E03043Q0069636F6E03263Q00496E746572666163655C42752Q746F6E735C55492D47726F75704C2Q6F742D446963652D557003073Q004F6E436C69636B030D3Q004F6E542Q6F6C74697053686F7703083Q00526567697374657201224Q006300015Q0020330001000100012Q00560001000200020006620001000600013Q00047B3Q000600012Q006A3Q00013Q00126E000100023Q001274000200034Q0070000300014Q003500010003000200065E00023Q000100012Q004F3Q00013Q00126E000300023Q001274000400044Q00560003000200020020330003000300052Q0063000500024Q004D00063Q00050030690006000600070030690006000800090030690006000A000B00065E00070001000100012Q00763Q00023Q0010570006000C0007000220000700023Q0010570006000D00072Q00350003000600022Q004D00045Q00203300050001000E2Q0063000700024Q000D000800034Q000D000900044Q002B0005000900012Q006A3Q00013Q00033Q00063Q00030A3Q0053746F72654672616D65030C3Q00476574412Q7472696275746503073Q00692Q73686F776E030A3Q004C65667442752Q746F6E030B3Q00526967687442752Q746F6E030C3Q0053652Q74696E677353686F77021A3Q00126E000200013Q0006620002000A00013Q00047B3Q000A000100126E000200013Q002033000200020002001274000400034Q00350002000400020006620002000A00013Q00047B3Q000A00012Q006A3Q00013Q0026533Q00160001000400047B3Q001600010006620001001000013Q00047B3Q00100001002653000100160001000400047B3Q001600010026533Q00160001000500047B3Q001600010006620001001900013Q00047B3Q0019000100262F000100190001000500047B3Q001900012Q006300025Q0020430002000200062Q00400002000100012Q006A3Q00019Q002Q0002044Q006300026Q000D000300014Q002A0002000200012Q006A3Q00017Q00023Q0003073Q00412Q644C696E65030C3Q004865726F526F746174696F6E010A3Q0006623Q000500013Q00047B3Q0005000100204300013Q0001000668000100060001000100047B3Q000600012Q006A3Q00013Q00203300013Q0001001274000300024Q002B0001000300012Q006A3Q00017Q00013Q00030C3Q005F4368696C6450616E656C5F01084Q006300016Q0063000200013Q001274000300014Q000D00046Q006D0002000200042Q006B0001000100022Q0073000100024Q006A3Q00017Q00053Q00030F3Q004372656174654D61696E50616E656C03053Q0050616E656C03043Q006773756203013Q0020034Q0005104Q006300016Q0063000500013Q0020330005000500012Q00560005000200022Q0063000600013Q0010570006000200052Q0002000300024Q0002000400034Q0063000600043Q002033000700010003001274000900043Q001274000A00054Q00350007000A00022Q003E0006000700052Q0073000500024Q006A3Q00017Q00063Q0003073Q004765744E616D6503083Q004D616B6550616765030C3Q005F4368696C6450616E656C5F03043Q006773756203013Q0020034Q0002133Q00203300023Q00012Q00560002000200022Q000D000300014Q006300045Q0020330004000400022Q000D000600034Q000D000700024Q00350004000700022Q0063000500014Q000D000600023Q001274000700033Q002033000800030004001274000A00053Q001274000B00064Q00350008000B00022Q006D0006000600082Q003E0005000600042Q0073000400024Q006A3Q00017Q00013Q00026Q00F03F01154Q004D00026Q001C00036Q000700023Q00012Q000D00036Q0059000300010002001274000400014Q001E000500023Q002008000500050001001274000600013Q0004050004000D00012Q006B0008000200072Q006B0003000300080004250004000A00012Q006300046Q001E000500024Q006B0005000200052Q00560004000200022Q000D000500034Q000D000600044Q007A000500034Q006A3Q00017Q00373Q0003073Q0063752Q72656E7403073Q004765744E616D6503013Q0079025Q00804140025Q00807DC0025Q008047C003013Q0078025Q00207740030B3Q004372656174654672616D6503063Q00536C6964657203073Q0024706172656E7403153Q004F7074696F6E73536C6964657254656D706C61746503083Q00536574506F696E7403073Q00544F504C454654026Q002E40026Q00344003013Q002E030F3Q005365744D696E4D617856616C756573026Q00F03F027Q004003083Q006D696E56616C756503083Q006D617856616C7565030F3Q004765744D696E4D617856616C75657303083Q0053657456616C7565030C3Q0053657456616C756553746570026Q00084003113Q005365744F626579537465704F6E4472616703023Q005F472Q033Q004C6F7703073Q005365745465787403043Q004869676803103Q00437265617465466F6E74537472696E6703073Q00415254574F524B03163Q0047616D65466F6E74486967686C69676874536D612Q6C2Q033Q00544F5003063Q00424F2Q544F4D028Q0003083Q005365745769647468026Q004940030B3Q005365744A7573746966794803063Q0043454E54455203043Q00252E3066030E3Q0047616D65466F6E744E6F726D616C030A3Q00424F2Q544F4D4C45465403043Q004C454654030E3Q0052656C6F6164526571756972656403013Q002A03063Q007C6E7C6E2A2003133Q0052657175697265732055492072656C6F61642E03093Q0053657453637269707403073Q004F6E456E74657203063Q00546970532Q6503073Q004F6E4C6561766503103Q0047616D65542Q6F6C7469705F48696465030E3Q004F6E56616C75654368616E67656407CD4Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B0007000700082Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B0008000800090020430008000800030020080008000800040010570007000300082Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B00070007000800204300070007000300265B000700210001000500047B3Q002100012Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B0007000700080030690007000300062Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B00070007000800306900070007000800126E000700093Q0012740008000A3Q0012740009000B4Q0063000A00014Q0059000A000100022Q006D00090009000A2Q000D000A5Q001274000B000C4Q00350007000B000200203300080007000D001274000A000E4Q0063000B5Q002043000B000B0001002033000C3Q00022Q0056000C000200022Q006B000B000B000C002043000B000B0007002009000B000B000F2Q0063000C5Q002043000C000C0001002033000D3Q00022Q0056000D000200022Q006B000C000C000D002043000C000C00032Q002B0008000C00012Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B0008000800092Q006300095Q002043000900090001002033000A3Q00022Q0056000A000200022Q006B00090009000A0020430009000900030020080009000900100010570008000300092Q0063000800024Q0063000900034Q0063000A00043Q001274000B00114Q000D000C00014Q001F000A000C4Q002C00083Q0009002033000A00070012002043000C00020013002043000D000200142Q002B000A000D0001002033000A000700172Q003A000A0002000B00105700070016000B00105700070015000A002033000A000700182Q006B000C000800092Q002B000A000C0001002033000A00070019002043000C0002001A2Q002B000A000C0001002033000A0007001B2Q0070000C00014Q002B000A000C0001002033000A000700022Q0056000A0002000200126E000B001C4Q000D000C000A3Q001274000D001D4Q006D000C000C000D2Q006B000B000B000C002033000B000B001E002043000D000700152Q002B000B000D000100126E000B001C4Q000D000C000A3Q001274000D001F4Q006D000C000C000D2Q006B000B000B000C002033000B000B001E002043000D000700162Q002B000B000D0001002033000B000700202Q0024000D000D3Q001274000E00213Q001274000F00224Q0035000B000F0002002033000C000B000D001274000E00234Q000D000F00073Q001274001000243Q001274001100253Q001274001200254Q002B000C00120001002033000C000B0026001274000E00274Q002B000C000E0001002033000C000B0028001274000E00294Q002B000C000E0001002033000C000B001E2Q0063000E00053Q001274000F002A4Q006B0010000800092Q001F000E00104Q0031000C3Q0001002033000C000700202Q0024000E000E3Q001274000F00213Q0012740010002B4Q0035000C00100002002033000D000C000D001274000F002C4Q000D001000073Q0012740011000E4Q002B000D00110001002033000D000C0028001274000F002D4Q002B000D000F00012Q0024000D000D3Q000662000600B000013Q00047B3Q00B00001002043000E0006002E000662000E00B000013Q00047B3Q00B00001002033000E000C001E2Q000D001000033Q0012740011002F4Q006D0010001000112Q002B000E001000012Q0063000E00063Q002033000F000700022Q0056000F000200022Q000D001000043Q001274001100303Q001274001200314Q006D0010001000122Q003E000E000F001000065E000D3Q000100052Q004F3Q00074Q00763Q00014Q00763Q000B4Q004F3Q00054Q00763Q00053Q00047B3Q00BF0001002033000E000C001E2Q000D001000034Q002B000E001000012Q0063000E00063Q002033000F000700022Q0056000F000200022Q003E000E000F000400065E000D0001000100072Q00763Q00084Q00763Q00094Q004F3Q00074Q00763Q00014Q00763Q00054Q00763Q000B4Q004F3Q00053Q002033000E00070032001274001000334Q006300115Q0020430011001100342Q002B000E00110001002033000E00070032001274001000353Q00126E001100364Q002B000E00110001002033000E00070032001274001000374Q000D0011000D4Q002B000E001100012Q006A3Q00013Q00023Q00033Q0003083Q0047657456616C756503073Q005365745465787403043Q00252E306601143Q00203300013Q00012Q00560001000200022Q006300026Q0063000300014Q003E0002000300012Q0063000200023Q0020330002000200022Q0063000400033Q001274000500034Q000D000600014Q001F000400064Q003100023Q00012Q0063000200043Q0006620002001300013Q00047B3Q001300012Q0063000200043Q00203300033Q00012Q000A000300044Q003100023Q00012Q006A3Q00017Q00033Q0003083Q0047657456616C756503073Q005365745465787403043Q00252E306601173Q00203300013Q00012Q00560001000200022Q006300026Q0063000300014Q003E0002000300012Q0063000200024Q0063000300034Q003E0002000300012Q0063000200043Q0006620002000F00013Q00047B3Q000F00012Q0063000200043Q00203300033Q00012Q000A000300044Q003100023Q00012Q0063000200053Q0020330002000200022Q0063000400063Q001274000500034Q000D000600014Q001F000400064Q003100023Q00012Q006A3Q00017Q00243Q0003073Q0063752Q72656E7403073Q004765744E616D6503013Q0079026Q002440025Q00807DC0025Q008047C003013Q0078025Q00207740030B3Q004372656174654672616D65030B3Q00436865636B42752Q746F6E03073Q0024706172656E7403233Q00496E746572666163654F7074696F6E73436865636B42752Q746F6E54656D706C61746503083Q00536574506F696E7403073Q00544F504C454654026Q00344003013Q002E030A3Q00536574436865636B656403023Q005F4703043Q005465787403103Q00437265617465466F6E74537472696E6703073Q00415254574F524B03113Q0047616D65466F6E74486967686C6967687403043Q004C454654026Q003940028Q00030E3Q0052656C6F6164526571756972656403073Q005365745465787403013Q002A03063Q007C6E7C6E2A2003133Q0052657175697265732055492072656C6F61642E03093Q0053657453637269707403073Q004F6E456E74657203063Q00546970532Q6503073Q004F6E4C6561766503103Q0047616D65542Q6F6C7469705F4869646503073Q006F6E436C69636B05A64Q006300055Q00204300050005000100203300063Q00022Q00560006000200022Q006B0005000500062Q006300065Q00204300060006000100203300073Q00022Q00560007000200022Q006B0006000600070020430006000600030020080006000600040010570005000300062Q006300055Q00204300050005000100203300063Q00022Q00560006000200022Q006B00050005000600204300050005000300265B000500210001000500047B3Q002100012Q006300055Q00204300050005000100203300063Q00022Q00560006000200022Q006B0005000500060030690005000300062Q006300055Q00204300050005000100203300063Q00022Q00560006000200022Q006B0005000500060030690005000700082Q0024000500053Q00126E000600093Q0012740007000A3Q0012740008000B4Q0063000900014Q00590009000100022Q006D0008000800092Q000D00095Q001274000A000C4Q00350006000A000200203300070006000D0012740009000E4Q0063000A5Q002043000A000A0001002033000B3Q00022Q0056000B000200022Q006B000A000A000B002043000A000A0007002009000A000A000F2Q0063000B5Q002043000B000B0001002033000C3Q00022Q0056000C000200022Q006B000B000B000C002043000B000B00032Q002B0007000B00012Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B0007000700082Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B0008000800090020430008000800030020080008000800040010570007000300082Q0063000700024Q0063000800034Q0063000900043Q001274000A00104Q000D000B00014Q001F0009000B4Q002C00073Q00080020330009000600112Q006B000B000700082Q002B0009000B000100126E000900123Q002033000A000600022Q0056000A00020002001274000B00134Q006D000A000A000B002033000B000600142Q0024000D000D3Q001274000E00153Q001274000F00164Q0035000B000F00022Q003E0009000A000B00126E000900123Q002033000A000600022Q0056000A00020002001274000B00134Q006D000A000A000B2Q006B00090009000A00203300090009000D001274000B00173Q001274000C00183Q001274000D00194Q002B0009000D00010006620004008600013Q00047B3Q0086000100204300090004001A0006620009008600013Q00047B3Q0086000100126E000900123Q002033000A000600022Q0056000A00020002001274000B00134Q006D000A000A000B2Q006B00090009000A00203300090009001B2Q000D000B00023Q001274000C001C4Q006D000B000B000C2Q002B0009000B000100065E00053Q000100042Q004F3Q00054Q00763Q00014Q00763Q00074Q00763Q00084Q0063000900063Q002033000A000600022Q0056000A000200022Q000D000B00033Q001274000C001D3Q001274000D001E4Q006D000B000B000D2Q003E0009000A000B00047B3Q0098000100126E000900123Q002033000A000600022Q0056000A00020002001274000B00134Q006D000A000A000B2Q006B00090009000A00203300090009001B2Q000D000B00024Q002B0009000B000100065E00050001000100042Q00763Q00074Q00763Q00084Q004F3Q00054Q00763Q00014Q0063000900063Q002033000A000600022Q0056000A000200022Q003E0009000A000300203300090006001F001274000B00204Q0063000C5Q002043000C000C00212Q002B0009000C000100203300090006001F001274000B00223Q00126E000C00234Q002B0009000C000100203300090006001F001274000B00244Q000D000C00054Q002B0009000C00012Q006A3Q00013Q00027Q0001084Q006300016Q0063000200014Q0063000300024Q0063000400034Q006B0003000300042Q007F000300034Q003E0001000200032Q006A3Q00019Q002Q00010B4Q006300016Q0063000200014Q006B0001000100022Q007F000100014Q006300026Q0063000300014Q003E0002000300012Q0063000200024Q0063000300034Q003E0002000300012Q006A3Q00017Q00253Q0003073Q0063752Q72656E7403073Q004765744E616D6503013Q0079025Q00804140025Q00807DC0026Q0057C003013Q0078025Q00207740030B3Q004372656174654672616D6503053Q004672616D6503073Q0024706172656E7403163Q00554944726F70446F776E4D656E7554656D706C61746503083Q00536574506F696E7403073Q00544F504C454654026Q002E4003013Q002E03103Q00437265617465466F6E74537472696E6703073Q00415254574F524B030E3Q0047616D65466F6E744E6F726D616C030E3Q0052656C6F6164526571756972656403073Q005365745465787403013Q002A03063Q007C6E7C6E2A2003133Q0052657175697265732055492072656C6F61642E03193Q00554944726F70446F776E4D656E755F496E697469616C697A65031F3Q00554944726F70446F776E4D656E755F53657453656C656374656456616C7565031A3Q00554944726F70446F776E4D656E755F4A7573746966795465787403043Q004C454654030A3Q00424F2Q544F4D4C454654026Q003440026Q001440030B3Q005365744A7573746966794803093Q0053657453637269707403073Q004F6E456E746572030B3Q0053686F7744726F7054697003073Q004F6E4C6561766503103Q0047616D65542Q6F6C7469705F4869646506A84Q006300065Q00204300060006000100203300073Q00022Q00560007000200022Q006B0006000600072Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B0007000700080020430007000700030020080007000700040010570006000300072Q006300065Q00204300060006000100203300073Q00022Q00560007000200022Q006B00060006000700204300060006000300265B000600210001000500047B3Q002100012Q006300065Q00204300060006000100203300073Q00022Q00560007000200022Q006B0006000600070030690006000300062Q006300065Q00204300060006000100203300073Q00022Q00560007000200022Q006B00060006000700306900060007000800126E000600093Q0012740007000A3Q0012740008000B4Q0063000900014Q00590009000100022Q006D0008000800092Q000D00095Q001274000A000C4Q00350006000A000200203300070006000D0012740009000E4Q0063000A5Q002043000A000A0001002033000B3Q00022Q0056000B000200022Q006B000A000A000B002043000A000A00072Q0063000B5Q002043000B000B0001002033000C3Q00022Q0056000C000200022Q006B000B000B000C002043000B000B00032Q002B0007000B00012Q006300075Q00204300070007000100203300083Q00022Q00560008000200022Q006B0007000700082Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B00080008000900204300080008000300200800080008000F0010570007000300082Q0063000700024Q0063000800034Q0063000900043Q001274000A00104Q000D000B00014Q001F0009000B4Q002C00073Q00082Q0024000900093Q002033000A000600112Q0063000C00014Q0059000C00010002001274000D00123Q001274000E00134Q0035000A000E00020006620005006B00013Q00047B3Q006B0001002043000B00050014000662000B006B00013Q00047B3Q006B0001002033000B000A00152Q000D000D00033Q001274000E00164Q006D000D000D000E2Q002B000B000D00012Q0063000B00053Q002033000C000A00022Q0056000C000200022Q000D000D00043Q001274000E00173Q001274000F00184Q006D000D000D000F2Q003E000B000C000D00065E00093Q000100032Q00763Q00064Q004F3Q00064Q00763Q00013Q00047B3Q00780001002033000B000A00152Q000D000D00034Q002B000B000D00012Q0063000B00053Q002033000C000A00022Q0056000C000200022Q003E000B000C000400065E00090001000100052Q00763Q00064Q00763Q00074Q00763Q00084Q004F3Q00064Q00763Q00013Q00065E000B0002000100022Q00763Q00024Q00763Q00093Q00126E000C00194Q000D000D00064Q000D000E000B4Q002B000C000E000100126E000C001A4Q000D000D00064Q006B000E000700082Q002B000C000E000100126E000C001B4Q000D000D00063Q001274000E001C4Q002B000C000E0001002033000C000A000D001274000E001D4Q000D000F00063Q0012740010000E3Q0012740011001E3Q0012740012001F4Q002B000C00120001002033000C000A0020001274000E001C4Q002B000C000E0001002033000C000A0021001274000E00224Q0063000F5Q002043000F000F00232Q002B000C000F0001002033000C000A0021001274000E00243Q00126E000F00254Q002B000C000F00012Q0063000C00053Q002033000D000600022Q0056000D000200022Q003E000C000D0004002033000C00060021001274000E00224Q0063000F5Q002043000F000F00232Q002B000C000F0001002033000C00060021001274000E00243Q00126E000F00254Q002B000C000F00012Q006A3Q00013Q00033Q00033Q00031C3Q00554944726F70446F776E4D656E755F53657453656C6563746564494403053Q00476574494403163Q00554944726F70446F776E4D656E755F47657454657874010C3Q00126E000100014Q006300025Q00203300033Q00022Q000A000300044Q003100013Q00012Q0063000100014Q0063000200023Q00126E000300034Q006300046Q00560003000200022Q003E0001000200032Q006A3Q00017Q00033Q00031C3Q00554944726F70446F776E4D656E755F53657453656C6563746564494403053Q00476574494403163Q00554944726F70446F776E4D656E755F47657454657874010F3Q00126E000100014Q006300025Q00203300033Q00022Q000A000300044Q003100013Q000100126E000100034Q006300026Q00560001000200022Q0063000200014Q0063000300024Q003E0002000300012Q0063000200034Q0063000300044Q003E0002000300012Q006A3Q00017Q00063Q0003193Q00554944726F70446F776E4D656E755F437265617465496E666F03053Q00706169727303043Q007465787403053Q0076616C756503043Q0066756E6303183Q00554944726F70446F776E4D656E755F412Q6442752Q746F6E02143Q00126E000200014Q005900020001000200126E000300024Q006300046Q003A00030002000500047B3Q0011000100126E000800014Q00590008000100022Q000D000200083Q0010570002000300070010570002000400072Q0063000800013Q00105700020005000800126E000800064Q000D000900024Q000D000A00014Q002B0008000A0001000614000300060001000200047B3Q000600012Q006A3Q00017Q001F3Q0003073Q0063752Q72656E7403073Q004765744E616D6503013Q0079026Q002440025Q00807DC0025Q008047C003013Q0078025Q00207740030B3Q004372656174654672616D6503063Q0042752Q746F6E03073Q0024706172656E7403153Q00554950616E656C42752Q746F6E54656D706C61746503083Q00536574506F696E7403073Q00544F504C454654026Q00344003083Q005365745769647468025Q00C0624003093Q00536574486569676874030E3Q0052656C6F6164526571756972656403023Q005F4703043Q005465787403073Q005365745465787403013Q002A03063Q007C6E7C6E2A2003133Q0052657175697265732055492072656C6F61642E03093Q0053657453637269707403073Q004F6E456E74657203063Q00546970532Q6503073Q004F6E4C6561766503103Q0047616D65542Q6F6C7469705F4869646503073Q006F6E436C69636B088D4Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B0008000800092Q006300095Q002043000900090001002033000A3Q00022Q0056000A000200022Q006B00090009000A0020430009000900030020080009000900040010570008000300092Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B00080008000900204300080008000300265B000800210001000500047B3Q002100012Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B0008000800090030690008000300062Q006300085Q00204300080008000100203300093Q00022Q00560009000200022Q006B00080008000900306900080007000800126E000800093Q0012740009000A3Q001274000A000B4Q0063000B00014Q0059000B000100022Q006D000A000A000B2Q000D000B5Q001274000C000C4Q00350008000C000200203300090008000D001274000B000E4Q0063000C5Q002043000C000C0001002033000D3Q00022Q0056000D000200022Q006B000C000C000D002043000C000C0007002009000C000C000F2Q0063000D5Q002043000D000D0001002033000E3Q00022Q0056000E000200022Q006B000D000D000E002043000D000D00032Q002B0009000D00012Q006300095Q002043000900090001002033000A3Q00022Q0056000A000200022Q006B00090009000A2Q0063000A5Q002043000A000A0001002033000B3Q00022Q0056000B000200022Q006B000A000A000B002043000A000A0003002008000A000A000400105700090003000A0006620005004D00013Q00047B3Q004D00010020330009000800102Q000D000B00054Q002B0009000B000100047B3Q00500001002033000900080010001274000B00114Q002B0009000B00010006620006005600013Q00047B3Q005600010020330009000800122Q000D000B00064Q002B0009000B000100047B3Q00590001002033000900080012001274000B000F4Q002B0009000B00010006620007007200013Q00047B3Q007200010020430009000700130006620009007200013Q00047B3Q0072000100126E000900143Q002033000A000800022Q0056000A00020002001274000B00154Q006D000A000A000B2Q006B00090009000A0020330009000900162Q000D000B00023Q001274000C00174Q006D000B000B000C2Q002B0009000B00012Q0063000900023Q002033000A000800022Q0056000A000200022Q000D000B00033Q001274000C00183Q001274000D00194Q006D000B000B000D2Q003E0009000A000B00047B3Q007F000100126E000900143Q002033000A000800022Q0056000A00020002001274000B00154Q006D000A000A000B2Q006B00090009000A0020330009000900162Q000D000B00024Q002B0009000B00012Q0063000900023Q002033000A000800022Q0056000A000200022Q003E0009000A000300203300090008001A001274000B001B4Q0063000C5Q002043000C000C001C2Q002B0009000C000100203300090008001A001274000B001D3Q00126E000C001E4Q002B0009000C000100203300090008001A001274000B001F4Q000D000C00044Q002B0009000C00012Q006A3Q00019Q002Q0001054Q006300026Q006B000200024Q001C00036Q003100023Q00012Q006A3Q00017Q000D3Q00026Q004AC003053Q007461626C6503063Q00696E73657274030A3Q0048692Q64656E4D656E7503073Q004765744E616D6503043Q006D656E7503043Q004869646503053Q00706169727303053Q00506167657303083Q00536574506F696E7403073Q00544F504C454654026Q003040026Q00344001353Q0006623Q003400013Q00047B3Q00340001001274000100013Q00126E000200023Q0020430002000200032Q006300035Q00204300030003000400203300043Q00052Q000A000400054Q003100023Q00012Q006300025Q00204300020002000600203300033Q00052Q00560003000200022Q006B0002000200030020330002000200072Q002A00020002000100126E000200084Q006300035Q0020430003000300092Q003A00020002000400047B3Q003200010006620006003200013Q00047B3Q003200012Q007000075Q00126E000800084Q006300095Q0020430009000900042Q003A00080002000A00047B3Q00230001002033000D000600052Q0056000D0002000200064C000C00230001000D00047B3Q002300012Q0070000700013Q0006140008001E0001000200047B3Q001E0001000668000700320001000100047B3Q003200012Q006300085Q0020430008000800060020330009000600052Q00560009000200022Q006B00080008000900203300080008000A001274000A000B3Q001274000B000C4Q000D000C00014Q002B0008000C000100200800010001000D000614000200160001000200047B3Q001600012Q006A3Q00017Q000E3Q00026Q004AC003063Q00697061697273030A3Q0048692Q64656E4D656E7503073Q004765744E616D6503053Q007461626C6503063Q0072656D6F766503043Q006D656E7503043Q0053686F7703053Q00706169727303053Q00506167657303083Q00536574506F696E7403073Q00544F504C454654026Q003040026Q003440013F3Q0006623Q003E00013Q00047B3Q003E0001001274000100013Q00126E000200024Q006300035Q0020430003000300032Q003A00020002000400047B3Q0012000100203300073Q00042Q005600070002000200064C000600120001000700047B3Q0012000100126E000700053Q0020430007000700062Q006300085Q0020430008000800032Q000D000900054Q002B000700090001000614000200080001000200047B3Q000800012Q006300025Q00204300020002000700203300033Q00042Q00560003000200022Q006B0002000200030020330002000200082Q002A00020002000100126E000200094Q006300035Q00204300030003000A2Q003A00020002000400047B3Q003C00010006620006003C00013Q00047B3Q003C00012Q007000075Q00126E000800094Q006300095Q0020430009000900032Q003A00080002000A00047B3Q002D0001002033000D000600042Q0056000D0002000200064C000C002D0001000D00047B3Q002D00012Q0070000700013Q000614000800280001000200047B3Q002800010006680007003C0001000100047B3Q003C00012Q006300085Q0020430008000800070020330009000600042Q00560009000200022Q006B00080008000900203300080008000B001274000A000C3Q001274000B000D4Q000D000C00014Q002B0008000C000100200800010001000E000614000200200001000200047B3Q002000012Q006A3Q00017Q00083Q00034Q0003053Q00706169727303013Q002E03043Q007479706503053Q007461626C6503173Q004C6F616453652Q74696E67735265637572736976656C79030B3Q0047554953652Q74696E677300022B3Q00062E000200030001000100047B3Q00030001001274000200013Q00126E000300024Q000D00046Q003A00030002000500047B3Q002800012Q0024000800083Q0026530002000F0001000100047B3Q000F00012Q000D000900023Q001274000A00034Q000D000B00064Q006D00080009000B00047B3Q001000012Q000D000800063Q00126E000900044Q000D000A00074Q005600090002000200262F0009001B0001000500047B3Q001B00012Q006300095Q0020430009000900062Q000D000A00074Q000D000B00084Q002B0009000B000100047B3Q002800012Q0063000900014Q000D000A00064Q00560009000200022Q0063000A00023Q002043000A000A00072Q006B000A000A0008002653000A00250001000800047B3Q002500012Q003E3Q0009000A00047B3Q002800012Q0063000B00023Q002043000B000B00072Q003E000B00080007000614000300070001000200047B3Q000700012Q006A3Q00017Q00013Q0003173Q0053686F7720474344206173204F2Q66204743443A20257301064Q006300015Q001274000200014Q000D00036Q0015000100034Q001200016Q006A3Q00017Q00013Q0003583Q00456E61626C6520696620796F752077616E7420746F207075742025732073686F776E206173204F2Q66204743442028746F702069636F6E732920696E7374656164206F66204D61696E20284D692Q646C652069636F6E292E01064Q006300015Q001274000200014Q000D00036Q0015000100034Q001200016Q006A3Q00017Q00013Q00031B3Q0053686F77204F2Q6620474344206173204F2Q66204743443A20257301064Q006300015Q001274000200014Q000D00036Q0015000100034Q001200016Q006A3Q00017Q00013Q0003583Q00456E61626C6520696620796F752077616E7420746F207075742025732073686F776E206173204F2Q66204743442028746F702069636F6E732920696E7374656164206F66204D61696E20284D692Q646C652069636F6E292E01064Q006300015Q001274000200014Q000D00036Q0015000100034Q001200016Q006A3Q00017Q00043Q00030B3Q00436865636B42752Q746F6E03053Q005573653A20031A3Q00456E61626C6520696620796F752077616E7420746F207573652003013Q002E030D4Q006300035Q001274000400014Q000D00056Q000D000600013Q001274000700024Q000D000800024Q006D000700070008001274000800034Q000D000900023Q001274000A00044Q006D00080008000A2Q002B0003000800012Q006A3Q00017Q00063Q0003063Q00536C69646572028Q00026Q004E40026Q00F03F030C3Q002054696D6520546F20446965031D3Q0054696D6520746F204469652072656D61696E696E6720746F207573652003114Q006300035Q001274000400014Q000D00056Q000D000600014Q004D000700033Q001274000800023Q001274000900033Q001274000A00046Q0007000300012Q000D000800023Q001274000900054Q006D000800080009001274000900064Q000D000A00024Q006D00090009000A2Q002B0003000900012Q006A3Q00017Q00063Q0003063Q00536C69646572028Q00026Q005940026Q00F03F03153Q00204865616C74682050657263656E7420557361676503263Q004865616C74682050657263656E7420746F2075736520646566656E73697665207370652Q6C2003114Q006300035Q001274000400014Q000D00056Q000D000600014Q004D000700033Q001274000800023Q001274000900033Q001274000A00046Q0007000300012Q000D000800023Q001274000900054Q006D000800080009001274000900064Q000D000A00024Q006D00090009000A2Q002B0003000900012Q006A3Q00017Q00073Q0003083Q0044726F70646F776E030E3Q005769746820432Q6F6C646F776E7303063Q00416C7761797303053Q004E6576657203073Q0055736167653A2003143Q00432Q6F6C646F776E7320557361676520666F722003013Q002E03124Q006300035Q001274000400014Q000D00056Q000D000600014Q004D000700033Q001274000800023Q001274000900033Q001274000A00046Q000700030001001274000800054Q000D000900024Q006D000800080009001274000900064Q000D000A00023Q001274000B00074Q006D00090009000B2Q002B0003000900012Q006A3Q00017Q00083Q0003083Q0044726F70646F776E03093Q004D61696E2049636F6E03093Q0053752Q676573746564030E3Q0053752Q676573746564526967687403083Q00432Q6F6C646F776E030F3Q00446973706C6179205374796C653A20032B3Q00446566696E652077686963682069636F6E20646973706C6179207374796C6520746F2075736520666F722003013Q002E03134Q006300035Q001274000400014Q000D00056Q000D000600014Q004D000700043Q001274000800023Q001274000900033Q001274000A00043Q001274000B00056Q000700040001001274000800064Q000D000900024Q006D000800080009001274000900074Q000D000A00023Q001274000B00084Q006D00090009000B2Q002B0003000900012Q006A3Q00017Q00063Q0003083Q0044726F70646F776E030F3Q0054656D706572656420506F74696F6E030D3Q00506F74696F6E20547970653A2003223Q00446566696E6520776869636820706F74696F6E207479706520746F20747261636B2E030E3Q0052656C6F616452657175697265642Q01030D4Q006300035Q001274000400014Q000D00056Q000D000600014Q004D000700013Q001274000800026Q000700010001001274000800033Q001274000900044Q004D000A3Q0001003069000A000500062Q002B0003000A00012Q006A3Q00017Q00093Q0003083Q0044726F70646F776E03013Q003103013Q003203013Q00332Q033Q00416E79030D3Q00506F74696F6E2052616E6B3A2003203Q00446566696E6520776869636820706F74696F6E2072616E6B20746F207573652E030E3Q0052656C6F616452657175697265642Q0103104Q006300035Q001274000400014Q000D00056Q000D000600014Q004D000700043Q001274000800023Q001274000900033Q001274000A00043Q001274000B00056Q000700040001001274000800063Q001274000900074Q004D000A3Q0001003069000A000800092Q002B0003000A00012Q006A3Q00017Q00193Q00030E3Q004175746F20496E74652Q72757074030B3Q00436865636B42752Q746F6E03263Q00496E74652Q7275707420544152474554207769746820696E74652Q72757074207370652Q6C2E03093Q004175746F205374756E031B3Q00496E74652Q72757074205441524745542077697468207374756E7303193Q00496E74652Q727570742045766572797468696E67205261696403233Q00496E74652Q727570742065766572797468696E67207768696C6520696E20726169642E03193Q00496E74652Q727570742045766572797468696E6720536F6C6F03203Q00496E74652Q727570742065766572797468696E67207768696C6520736F6C6F2E03143Q00496E74652Q7275707420496E2044756E67656F6E03083Q0044726F70646F776E03043Q004E6F6E65030A3Q0045766572797468696E6703093Q0057686974656C697374031D3Q00496E74652Q727570742073652Q74696E6720696E2064756E67656F6E2E032A3Q00496E74652Q7275707420496E2044756E67656F6E20557365205374756E20417320496E74652Q7275707403203Q00557365207374756E20617320696E74652Q7275707420696E2064756E67656F6E03113Q00496E74652Q727570742050657263656E7403063Q00536C69646572028Q00026Q005940026Q00F03F03363Q0050657263656E74616765206F662063617374206174207768696368206361737473206D75737420626520696E74652Q7275707465642E03193Q00496E74652Q727570742050657263656E74204368612Q6E656C033E3Q0050657263656E74616765206F662063617374206174207768696368206368612Q6E656C206361737473206D75737420626520696E74652Q7275707465642E035F3Q00262F0002000A0001000100047B3Q000A00012Q006300035Q001274000400024Q000D00056Q000D000600014Q000D000700023Q001274000800034Q002B00030008000100047B3Q005E000100262F000200140001000400047B3Q001400012Q006300035Q001274000400024Q000D00056Q000D000600014Q000D000700023Q001274000800054Q002B00030008000100047B3Q005E000100262F0002001E0001000600047B3Q001E00012Q006300035Q001274000400024Q000D00056Q000D000600014Q000D000700023Q001274000800074Q002B00030008000100047B3Q005E000100262F000200280001000800047B3Q002800012Q006300035Q001274000400024Q000D00056Q000D000600014Q000D000700023Q001274000800094Q002B00030008000100047B3Q005E000100262F000200370001000A00047B3Q003700012Q006300035Q0012740004000B4Q000D00056Q000D000600014Q004D000700033Q0012740008000C3Q0012740009000D3Q001274000A000E6Q0007000300012Q000D000800023Q0012740009000F4Q002B00030009000100047B3Q005E000100262F000200410001001000047B3Q004100012Q006300035Q001274000400024Q000D00056Q000D000600014Q000D000700023Q001274000800114Q002B00030008000100047B3Q005E000100262F000200500001001200047B3Q005000012Q006300035Q001274000400134Q000D00056Q000D000600014Q004D000700033Q001274000800143Q001274000900153Q001274000A00166Q0007000300012Q000D000800023Q001274000900174Q002B00030009000100047B3Q005E000100262F0002005E0001001800047B3Q005E00012Q006300035Q001274000400134Q000D00056Q000D000600014Q004D000700033Q001274000800143Q001274000900153Q001274000A00166Q0007000300012Q000D000800023Q001274000900194Q002B0003000900012Q006A3Q00017Q00013Q00030B3Q00436865636B42752Q746F6E030C4Q006300035Q001274000400014Q000D00056Q000D000600014Q0063000700014Q000D000800024Q00560007000200022Q0063000800024Q000D000900024Q000A000800094Q003100033Q00012Q006A3Q00017Q00013Q00030B3Q00436865636B42752Q746F6E030C4Q006300035Q001274000400014Q000D00056Q000D000600014Q0063000700014Q000D000800024Q00560007000200022Q0063000800024Q000D000900024Q000A000800094Q003100033Q00012Q006A3Q00019Q002Q0003074Q006300046Q006B000400044Q000D000500014Q000D000600024Q001C00076Q003100043Q00012Q006A3Q00017Q000D3Q0003013Q002E030E3Q0047554953652Q74696E6773476574026Q00F03F03053Q007061697273030C3Q0053652Q74696E67735479706503053Q007461626C6503063Q00696E7365727403043Q00736F727403063Q00697061697273034Q00030E3Q005B412D5A5D5B612D7A302D395D2B03013Q002003133Q00437265617465415250616E656C4F7074696F6E02514Q004D00026Q006300035Q001274000400014Q000D000500014Q001F000300054Q000700023Q00012Q0063000300013Q0020430003000300022Q0059000300010002001274000400034Q001E000500023Q001274000600033Q0004050004001000012Q006B0008000200072Q006B0003000300080004250004000D000100126E000400044Q0063000500024Q003A00040002000600047B3Q004E00012Q006B000900030007001258000900053Q00126E000900053Q0006620009004E00013Q00047B3Q004E00012Q004D00095Q00126E000A00043Q00126E000B00054Q003A000A0002000C00047B3Q0023000100126E000F00063Q002043000F000F00072Q000D001000094Q000D0011000D4Q002B000F00110001000614000A001E0001000200047B3Q001E000100126E000A00063Q002043000A000A00082Q000D000B00094Q002A000A0002000100126E000A00094Q000D000B00094Q003A000A0002000C00047B3Q004C0001001274000F000A4Q0063001000034Q000D0011000E3Q0012740012000B4Q007700100012001200047B3Q003B000100262F000F00370001000A00047B3Q003700012Q000D000F00133Q00047B3Q003B00012Q000D0014000F3Q0012740015000C4Q000D001600134Q006D000F00140016000614001000330001000100047B3Q003300012Q0063001000044Q004D001100034Q000D001200014Q000D001300074Q000D0014000E6Q001100030001001274001200014Q00350010001200022Q0063001100053Q00204300110011000D2Q000D001200074Q000D00136Q000D001400104Q000D0015000F4Q002B001100150001000614000A002D0001000200047B3Q002D0001000614000400140001000200047B3Q001400012Q006A3Q00017Q00", GetFEnv(), ...);