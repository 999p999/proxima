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
				if (Enum <= 24) then
					if (Enum <= 11) then
						if (Enum <= 5) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 1) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 3) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 4) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 7) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 9) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 10) then
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
								if (Mvm[1] == 37) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 17) then
						if (Enum <= 14) then
							if (Enum <= 12) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum == 13) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 15) then
							local VA;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 16) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 20) then
						if (Enum <= 18) then
							local A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								local VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
						elseif (Enum == 19) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							A = Inst[2];
							B = Inst[3];
							for Idx = A, B do
								Stk[Idx] = Vararg[Idx - A];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 22) then
						if (Enum == 21) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local A = Inst[2];
							local B = Inst[3];
							for Idx = A, B do
								Stk[Idx] = Vararg[Idx - A];
							end
						end
					elseif (Enum > 23) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					else
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 36) then
					if (Enum <= 30) then
						if (Enum <= 27) then
							if (Enum <= 25) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum == 26) then
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 28) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 29) then
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local Edx;
							local Results;
							local VA;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 33) then
						if (Enum <= 31) then
							local Edx;
							local Results;
							local VA;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 32) then
							local B;
							local Edx;
							local Results;
							local VA;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local Edx;
							local Results;
							local VA;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 34) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					elseif (Enum == 35) then
						local VA;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Top = (A + Varargsz) - 1;
						for Idx = A, Top do
							VA = Vararg[Idx - A];
							Stk[Idx] = VA;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 42) then
					if (Enum <= 39) then
						if (Enum <= 37) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum > 38) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local B;
							local Edx;
							local Results;
							local VA;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 40) then
						Stk[Inst[2]] = {};
					elseif (Enum == 41) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						do
							return;
						end
					end
				elseif (Enum <= 45) then
					if (Enum <= 43) then
						local VA;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Top = (A + Varargsz) - 1;
						for Idx = A, Top do
							VA = Vararg[Idx - A];
							Stk[Idx] = VA;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 44) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 47) then
					if (Enum > 46) then
						Stk[Inst[2]] = Inst[3];
					else
						local B;
						local Edx;
						local Results;
						local VA;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Top = (A + Varargsz) - 1;
						for Idx = A, Top do
							VA = Vararg[Idx - A];
							Stk[Idx] = VA;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum == 48) then
					if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Stk[Inst[2]] == Inst[4]) then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!263Q0003073Q004865726F4C6962030C3Q004865726F526F746174696F6E03093Q004865726F436163686503043Q00556E697403063Q00506C6179657203063Q0054617267657403053Q005370652Q6C03043Q004974656D03073Q0047657454696D6503073Q00435F54696D657203063Q0073656C65637403053Q00416674657203073Q00436F2Q6D6F6E7303063Q005368616D616E030A3Q004C617374534B43617374028Q00030A3Q004C617374534B42752Q6603163Q004C617374526F2Q6C696E675468756E6465725469636B03103Q00466572616C537069726974436F756E7403143Q00437261636B6C696E675375726765537461636B73030D3Q0049637945646765537461636B7303123Q004D6F6C74656E576561706F6E537461636B7303103Q0054656D706573744D61656C7374726F6D03123Q0053656172696E67546F74656D416374697665010003103Q0053656172696E67546F74656D47554944031A3Q005265676973746572466F7253656C66436F6D6261744576656E7403123Q005350452Q4C5F434153545F53552Q43452Q5303123Q005350452Q4C5F415552415F412Q504C49454403173Q005350452Q4C5F415552415F412Q504C4945445F444F5345030C3Q005350452Q4C5F53552Q4D4F4E03163Q005265676973746572466F72436F6D6261744576656E7403123Q005350452Q4C5F415552415F52454D4F564544030D3Q0046697265456C656D656E74616C030D3Q0047726561746572416374697665030C3Q004C652Q736572416374697665030E3Q0053746F726D456C656D656E74616C03093Q00554E49545F4449454400664Q00143Q00023Q00122Q000200013Q00122Q000300023Q00122Q000400033Q00202Q00050002000400202Q00060005000500202Q00070005000600202Q00080002000700202Q00090002000800122Q000A00093Q001210000B000A3Q00121E000C000B3Q00202Q000D000B000C00202Q000E0003000D4Q000F5Q00102Q000E000E000F00202Q000E0003000D00202Q000E000E000E00302Q000E000F001000302Q000E0011001000302Q000E0012001000302D000E00130010003002000E0014001000302Q000E0015001000302Q000E0016001000302Q000E0017001000302Q000E0018001900302Q000E001A001000202Q000F0002001B00060A00113Q000100042Q00253Q000C4Q00253Q00064Q00253Q000E4Q00253Q000A3Q00122F0012001C4Q002C000F00120001002017000F0002001B00060A00110001000100052Q00253Q000C4Q00253Q00064Q00253Q000E4Q00253Q000A4Q00253Q000D3Q00122F0012001D3Q00122F0013001E4Q002C000F00130001002017000F0002001B00060A00110002000100032Q00253Q000C4Q00253Q000E4Q00253Q000D3Q00122F0012001F4Q002C000F00120001002017000F0002002000060A00110003000100032Q00253Q000C4Q00253Q00064Q00253Q000E3Q00122F0012001D4Q002C000F00120001002017000F0002002000060A00110004000100032Q00253Q000C4Q00253Q00064Q00253Q000E3Q00121B001200216Q000F001200014Q000F3Q000200302Q000F0023001900302Q000F0024001900102Q000E0022000F4Q000F3Q000200302Q000F0023001900302Q000F0024001900102Q000E0025000F002017000F0002001B00060A00110005000100032Q00253Q000C4Q00253Q000E4Q00253Q000D3Q00122F0012001F4Q002C000F00120001002017000F0002001B00060A00110006000100022Q00253Q000C4Q00253Q000E3Q00122F0012001D3Q00122F0013001E4Q002C000F00130001002017000F0002001B00060A00110007000100022Q00253Q000C4Q00253Q000E3Q00122F0012001F4Q002C000F00120001002017000F0002002000060A00110008000100022Q00253Q000C4Q00253Q000E3Q00122F001200264Q002C000F001200012Q002A3Q00013Q00093Q00043Q00026Q00104003043Q0047554944024Q0090640741030A3Q004C617374534B4361737400104Q002E00015Q00122Q000200016Q00038Q00013Q00094Q000A00013Q00202Q000A000A00024Q000A0002000200062Q0001000F0001000A0004113Q000F00010026310009000F000100030004113Q000F00012Q0009000A00024Q0009000B00034Q0018000B00010002001003000A0004000B2Q002A3Q00017Q00053Q00026Q00204003043Q0047554944024Q0090640741030A3Q004C617374534B42752Q66029A5Q99B93F00154Q002E00015Q00122Q000200016Q00038Q00013Q00054Q000600013Q00202Q0006000600024Q00060002000200062Q00010014000100060004113Q0014000100263100050014000100030004113Q001400012Q0009000600024Q0015000700036Q00070001000200102Q0006000400074Q000600043Q00122Q000700053Q00060A00083Q000100012Q00093Q00024Q002C0006000800012Q002A3Q00013Q00013Q00033Q00030A3Q004C617374534B42752Q66030A3Q004C617374534B4361737403163Q004C617374526F2Q6C696E675468756E6465725469636B000B4Q000E7Q00206Q00014Q00015Q00202Q00010001000200064Q000A000100010004113Q000A00012Q00098Q000900015Q00200D0001000100010010033Q000300012Q002A3Q00017Q00083Q00026Q002840024Q008C071041024Q0050081A4103103Q00466572616C537069726974436F756E74026Q00F03F026Q002E40024Q0050A51C41026Q002040001F4Q002B00015Q00122Q000200016Q00038Q00013Q000200262Q00010008000100020004113Q0008000100263100010012000100030004113Q001200012Q0009000200014Q0027000300013Q00202Q00030003000400202Q00030003000500102Q0002000400034Q000200023Q00122Q000300063Q00060A00043Q000100012Q00093Q00014Q002C0002000400010026310001001E000100070004113Q001E00012Q0009000200014Q0027000300013Q00202Q00030003000400202Q00030003000500102Q0002000400034Q000200023Q00122Q000300083Q00060A00040001000100012Q00093Q00014Q002C0002000400012Q002A3Q00013Q00023Q00023Q0003103Q00466572616C537069726974436F756E74026Q00F03F00064Q00299Q0000015Q00202Q00010001000100202Q00010001000200104Q000100016Q00017Q00023Q0003103Q00466572616C537069726974436F756E74026Q00F03F00064Q00299Q0000015Q00202Q00010001000100202Q00010001000200104Q000100016Q00017Q00093Q00026Q00204003043Q0047554944024Q00E85B0B4103123Q004D6F6C74656E576561706F6E537461636B73026Q00F03F024Q00F05B0B41030D3Q0049637945646765537461636B73024Q00F85B0B4103143Q00437261636B6C696E675375726765537461636B7300214Q002E00015Q00122Q000200016Q00038Q00013Q00054Q000600013Q00202Q0006000600024Q00060002000200062Q00010020000100060004113Q0020000100263100050011000100030004113Q001100012Q0009000600024Q000C000700023Q00202Q00070007000400202Q00070007000500102Q00060004000700044Q0020000100263100050019000100060004113Q001900012Q0009000600024Q000C000700023Q00202Q00070007000700202Q00070007000500102Q00060007000700044Q0020000100263100050020000100080004113Q002000012Q0009000600024Q0009000700023Q00200D0007000700090020220007000700050010030006000900072Q002A3Q00017Q00093Q00026Q00204003043Q0047554944024Q00E85B0B4103123Q004D6F6C74656E576561706F6E537461636B73026Q00F03F024Q00F05B0B41030D3Q0049637945646765537461636B73024Q00F85B0B4103143Q00437261636B6C696E675375726765537461636B7300214Q002E00015Q00122Q000200016Q00038Q00013Q00054Q000600013Q00202Q0006000600024Q00060002000200062Q00010020000100060004113Q0020000100263100050011000100030004113Q001100012Q0009000600024Q0001000700023Q00202Q00070007000400202Q00070007000500102Q00060004000700044Q0020000100263100050019000100060004113Q001900012Q0009000600024Q0001000700023Q00202Q00070007000700202Q00070007000500102Q00060007000700044Q0020000100263100050020000100080004113Q002000012Q0009000600024Q0009000700023Q00200D00070007000900201A0007000700050010030006000900072Q002A3Q00017Q00103Q00026Q002040024Q0080050741024Q0030E1FC40030D3Q0046697265456C656D656E74616C030D3Q00477265617465724163746976652Q01026Q003840024Q0040421C41024Q003C421C41030C3Q004C652Q736572416374697665026Q002840024Q0098330341024Q0038340341030E3Q0053746F726D456C656D656E74616C024Q0044421C41024Q0038421C4100384Q001D00015Q00122Q000200016Q00038Q00013Q000500262Q00050008000100020004113Q0008000100263100050011000100030004113Q001100012Q0009000600013Q00200D00060006000400302D0006000500062Q0009000600023Q00122F000700073Q00060A00083Q000100012Q00093Q00014Q002C0006000800010004113Q0037000100260B00050015000100080004113Q001500010026310005001E000100090004113Q001E00012Q0009000600013Q00200D00060006000400302D0006000A00062Q0009000600023Q00122F0007000B3Q00060A00080001000100012Q00093Q00014Q002C0006000800010004113Q0037000100260B000500220001000C0004113Q002200010026310005002B0001000D0004113Q002B00012Q0009000600013Q00200D00060006000E00302D0006000500062Q0009000600023Q00122F000700073Q00060A00080002000100012Q00093Q00014Q002C0006000800010004113Q0037000100260B0005002F0001000F0004113Q002F000100263100050037000100100004113Q003700012Q0009000600013Q00200D00060006000E00302D0006000A00062Q0009000600023Q00122F0007000B3Q00060A00080003000100012Q00093Q00014Q002C0006000800012Q002A3Q00013Q00043Q00033Q00030D3Q0046697265456C656D656E74616C030D3Q0047726561746572416374697665012Q00044Q00097Q00200D5Q000100302D3Q000200032Q002A3Q00017Q00033Q00030D3Q0046697265456C656D656E74616C030C3Q004C652Q736572416374697665012Q00044Q00097Q00200D5Q000100302D3Q000200032Q002A3Q00017Q00033Q00030E3Q0053746F726D456C656D656E74616C030D3Q0047726561746572416374697665012Q00044Q00097Q00200D5Q000100302D3Q000200032Q002A3Q00017Q00033Q00030E3Q0053746F726D456C656D656E74616C030C3Q004C652Q736572416374697665012Q00044Q00097Q00200D5Q000100302D3Q000200032Q002A3Q00017Q00053Q00026Q002840024Q00CC01154103103Q0054656D706573744D61656C7374726F6D026Q00F03F026Q00444000154Q002300015Q00122Q000200016Q00038Q00013Q000200262Q00010014000100020004113Q001400012Q0009000200014Q0013000300013Q00202Q00030003000300202Q00030003000400102Q0002000300034Q000200013Q00202Q000200020003000E2Q00050014000100020004113Q001400012Q0009000200014Q0009000300013Q00200D00030003000300201A0003000300050010030002000300032Q002A3Q00017Q00063Q00026Q002040024Q00D4F51B41030D3Q0053656172696E6720546F74656D03123Q0053656172696E67546F74656D4163746976652Q0103103Q0053656172696E67546F74656D47554944000D4Q001F00015Q00122Q000200016Q00038Q00013Q000500262Q0005000C000100020004113Q000C00010026310002000C000100030004113Q000C00012Q0009000600013Q00302D0006000400052Q0009000600013Q0010030006000600012Q002A3Q00017Q00053Q00026Q00204003103Q0053656172696E67546F74656D4755494403123Q0053656172696E67546F74656D4163746976650100029Q000D4Q000F00015Q00122Q000200016Q00038Q00013Q00024Q000200013Q00202Q00020002000200062Q0001000C000100020004113Q000C00012Q0009000200013Q00302D0002000300042Q0009000200013Q00302D0002000200052Q002A3Q00017Q00", GetFEnv(), ...);